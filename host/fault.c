// 崩溃现场转储（独立编译单元：ucontext.h 在 macOS 需要 _XOPEN_SOURCE，
// 放这里定义避免影响主文件的符号可见性）。
#define _XOPEN_SOURCE 700
#define _DARWIN_C_SOURCE   // _XOPEN_SOURCE 下 macOS 头会藏起 Dl_info/dladdr（CI 新 clang 实证）
#include <dlfcn.h>
#include <signal.h>
#include <sys/time.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <ucontext.h>
#include <unistd.h>

typedef struct { char name[16]; uint8_t *base; size_t size; } mod_ref_t;
extern mod_ref_t g_mod_ref[8];
extern int g_nmod_ref;
extern int g_last_svc;
extern uint64_t g_guest_lo, g_guest_hi;   // dmhost 预留块区间（客体堆在内）
// 宿主移交登记（dmhost.c handout_reg）：崩溃寄存器里的宿主指针据此归属
typedef struct { const char *name; const void *lo, *hi; } handout_t;
extern handout_t g_handout[12];
extern int g_nhandout;

static void where_of(uint64_t a, char *out, size_t n) {
    for (int j = 0; j < g_nmod_ref; j++) {
        uint64_t b = (uint64_t)g_mod_ref[j].base;
        if (a >= b && a < b + g_mod_ref[j].size) { snprintf(out, n, "%s+%#llx", g_mod_ref[j].name, (unsigned long long)(a - b)); return; }
    }
    Dl_info di;   // 宿主映像/系统库：符号名解析（HLE 桩崩溃定位的关键）
    if (dladdr((void *)a, &di) && di.dli_sname)
        { snprintf(out, n, "%s+%#llx", di.dli_sname, (unsigned long long)(a - (uint64_t)di.dli_saddr)); return; }
    if (di.dli_fname)
        { snprintf(out, n, "%s+%#llx", di.dli_fname, (unsigned long long)(a - (uint64_t)di.dli_fbase)); return; }
    snprintf(out, n, "非模块区");
}

// 帧链回溯（x29 链），最多 8 层：LR 归属到模块。供 fault_dump 与 svc Break 共用。
void guest_backtrace(uint64_t fp) {
    uint64_t f = fp;
    for (int i = 0; i < 24 && f; i++) {
        uint64_t nxt = *(uint64_t *)f, ret = *(uint64_t *)(f + 8);
        char w2[64] = "";
        where_of(ret, w2, sizeof w2);
        fprintf(stderr, "[dm]   帧%d fp=%#llx lr=%#llx(%s)\n", i, (unsigned long long)f, (unsigned long long)ret, w2);
        if (nxt <= f) break;
        f = nxt;
    }
}

static void fault_dump(int sig, siginfo_t *si, void *uc_) {
    ucontext_t *uc = uc_;
    uint64_t pc = uc->uc_mcontext->__ss.__pc, lr = uc->uc_mcontext->__ss.__lr;
    uint64_t sp = uc->uc_mcontext->__ss.__sp, fp = uc->uc_mcontext->__ss.__fp;
    uint64_t x0 = uc->uc_mcontext->__ss.__x[0], x1 = uc->uc_mcontext->__ss.__x[1];
    uint64_t x2 = uc->uc_mcontext->__ss.__x[2], x3 = uc->uc_mcontext->__ss.__x[3];
    uint64_t x19 = uc->uc_mcontext->__ss.__x[19], x20 = uc->uc_mcontext->__ss.__x[20];
    char where[64];
    where_of(pc, where, sizeof where);
    fprintf(stderr, "[dm] FAULT sig=%d addr=%p pc=%#llx(%s) lr=%#llx sp=%#llx fp=%#llx x0=%#llx x1=%#llx x2=%#llx x3=%#llx 最近svc#%d\n",
            sig, si->si_addr, (unsigned long long)pc, where, (unsigned long long)lr,
            (unsigned long long)sp, (unsigned long long)fp,
            (unsigned long long)x0, (unsigned long long)x1, (unsigned long long)x2, (unsigned long long)x3, g_last_svc);
    fprintf(stderr, "[dm]   x19=%#llx x20=%#llx", (unsigned long long)x19, (unsigned long long)x20);
    if (x19 >= g_guest_lo && x19 < g_guest_hi) {   // 客体堆里的 ctx 对象：直接转储关键字段
        fprintf(stderr, "  [x19+0x90..0xc0]:");
        for (int o = 0x90; o <= 0xc0; o += 8)
            fprintf(stderr, " +%#x:%#llx", o, (unsigned long long)*(uint64_t *)(x19 + o));
    }
    fputc('\n', stderr);
    {   // 寄存器归属：x0..x28 里的宿主移交指针点名（宿主指针泄漏进客体数据 = 崩溃常见根因）
        const char *tag[29];
        int any = 0;
        for (int r = 0; r <= 28; r++) {
            uint64_t v = uc->uc_mcontext->__ss.__x[r];
            tag[r] = NULL;
            for (int j = 0; j < g_nhandout && !tag[r]; j++)
                if (v >= (uint64_t)g_handout[j].lo && v < (uint64_t)g_handout[j].hi)
                    tag[r] = g_handout[j].name;
        }
        fprintf(stderr, "[dm]   寄存器移交归属：");
        for (int r = 0; r <= 28; r++)
            if (tag[r]) { fprintf(stderr, " x%d∈%s", r, tag[r]); any = 1; }
        if (!any) fprintf(stderr, " 无");
        fputc('\n', stderr);
    }
    // 帧回溯取证：崩溃点在 sub(0x30) ← pool 建立函数(0x70) ← ctx 建立函数(0x30)；
    // 上一层函数把 ctx2 存在 [sp+0x88]（pool 函数的 x19 槽）与 [sp+0xb8]（ctx 函数的 x19 槽）
    for (int k = 0; k < 2; k++) {
        uint64_t slot = sp + (k ? 0xb8 : 0x88);
        uint64_t p = *(uint64_t *)slot;
        if (p >= g_guest_lo && p < g_guest_hi) {
            fprintf(stderr, "[dm]   [sp+%#x]=%#llx 的 [0x90..0xc0]:", k ? 0xb8 : 0x88, (unsigned long long)p);
            for (int o = 0x90; o <= 0xc0; o += 8)
                fprintf(stderr, " +%#x:%#llx", o, (unsigned long long)*(uint64_t *)(p + o));
            fputc('\n', stderr);
        }
    }
    guest_backtrace(fp);
    _exit(70);
}

static int wd_beats;
static void watchdog(int sig) {
    (void)sig;
    fprintf(stderr, "[dm] 心跳/看门狗 第 %d 分钟（最近svc#%d）\n", wd_beats + 1, g_last_svc);
    { void dm_dump_threads(void); dm_dump_threads(); }
    if (++wd_beats >= 10) {   // 10 分钟：CI 时限（15 分钟）前收尾
        fprintf(stderr, "[dm] 看门狗最终到期\n");
        _exit(71);
    }
}

static void on_host_exit(void) {
    fprintf(stderr, "[dm] 进程正常退出（exit/main 返回；最近svc#%d）\n", g_last_svc);
}
static void on_abort(int sig, siginfo_t *si, void *uc_) {
    // SIGTRAP = 客体 brk 指令（clang 的 trap/unreachable/断言）；带上现场再退
    if (sig == SIGTRAP && uc_) {
        ucontext_t *uc = uc_;
        uint64_t pc = uc->uc_mcontext->__ss.__pc, lr = uc->uc_mcontext->__ss.__lr;
        uint64_t sp = uc->uc_mcontext->__ss.__sp, fp = uc->uc_mcontext->__ss.__fp;
        uint64_t x0 = uc->uc_mcontext->__ss.__x[0], x1 = uc->uc_mcontext->__ss.__x[1];
        uint64_t x2 = uc->uc_mcontext->__ss.__x[2], x3 = uc->uc_mcontext->__ss.__x[3];
        char w[64];
        where_of(pc, w, sizeof w);
        fprintf(stderr, "[dm] HOST SIGTRAP pc=%#llx(%s) lr=%#llx sp=%#llx fp=%#llx x0=%#llx x1=%#llx x2=%#llx x3=%#llx 最近svc#%d\n",
                (unsigned long long)pc, w, (unsigned long long)lr, (unsigned long long)sp,
                (unsigned long long)fp, (unsigned long long)x0, (unsigned long long)x1,
                (unsigned long long)x2, (unsigned long long)x3, g_last_svc);
        guest_backtrace(fp);
        _exit(89);
    }
    fprintf(stderr, "[dm] HOST SIGABRT（最近svc#%d）\n", g_last_svc);
    _exit(88);
}

void diag_install(void) {
    struct sigaction sa = {0};
    sa.sa_sigaction = fault_dump;
    sa.sa_flags = SA_SIGINFO;
    sigaction(SIGSEGV, &sa, NULL);
    sigaction(SIGBUS, &sa, NULL);
    sigaction(SIGILL, &sa, NULL);
    sigaction(SIGFPE, &sa, NULL);
    struct sigaction sw = {0};
    sw.sa_handler = watchdog;
    sigaction(SIGALRM, &sw, NULL);
    {   // 60 秒重复心跳：每分钟转储线程落点，10 分钟终止（替代一次性 alarm）
        struct itimerval it = {60, 0, 60, 0};
        setitimer(ITIMER_REAL, &it, NULL);
    }
    struct sigaction ab = {0};
    ab.sa_sigaction = on_abort;
    ab.sa_flags = SA_SIGINFO;
    sigaction(SIGABRT, &ab, NULL);
    sigaction(SIGTRAP, &ab, NULL);
    atexit(on_host_exit);
}

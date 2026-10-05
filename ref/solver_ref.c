/* Reference build for Stage 3: the final C algorithm, compiled for RV32I.
 * No libc, no heap. Tables come from tables.h, generated on the host. */
#include <stdint.h>
#include "tables.h" /* perm_table, ori_table, permutation, orientation */

#ifndef INPUT
#define INPUT "21345671111111"
#endif

enum { CUBIES = 7, MAX_DEPTH = 11, NO_MOVE = 255 };

/* ---- Ripes environment calls ---- */
static inline void sys_print_string(const char *s)
{
    register const char *a0 __asm__("a0") = s;
    register int a7 __asm__("a7") = 4;
    __asm__ volatile("ecall" : "+r"(a0) : "r"(a7) : "memory");
}

static inline void sys_print_char(int c)
{
    register int a0 __asm__("a0") = c;
    register int a7 __asm__("a7") = 11;
    __asm__ volatile("ecall" : "+r"(a0) : "r"(a7) : "memory");
}

static inline void sys_exit(int code)
{
    register int a0 __asm__("a0") = code;
    register int a7 __asm__("a7") = 93;
    __asm__ volatile("ecall" : "+r"(a0) : "r"(a7) : "memory");
    for (;;)
        ;
}

static const char *const move_names[9] = {"R", "R2", "R'", "B", "B2",
                                          "B'", "D", "D2", "D'"};

/* ==== PASTE FROM stage3.c, in this order ====
 *   typedef struct { ... } state_t;
 *   typedef struct { ... } frame_t;
 *   valid()
 *   parse_state()
 *   the part of rank_state() that computes p and o
 *   heuristic()
 *   ida_search()
 * ============================================ */

static int run(void)
{
    state_t state;
    uint8_t solution[MAX_DEPTH];

    if (!parse_state(INPUT, &state))
        return 2; /* invalid input, same as solver.c */

    /* TODO (yours): compute the permutation rank p and the orientation rank o
     * from state, then call ida_search and store the length in `length`. */
    int length = -1;

    if (length < 0)
        return 1;
    for (int i = 0; i < length; ++i) {
        sys_print_string(move_names[solution[i]]);
        sys_print_char(i + 1 < length ? ' ' : '\n');
    }
    return 0;
}

void _start(void)
{
    sys_exit(run());
}
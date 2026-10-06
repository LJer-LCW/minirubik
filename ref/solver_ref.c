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

typedef struct {
    uint8_t p[CUBIES], o[CUBIES];
} state_t;

typedef struct {
    uint16_t perm;
    uint16_t ori;
    uint8_t move;
    uint8_t next_move;
} frame_t;

static int valid(const state_t *state)
{
    uint8_t sum = 0;
    for (uint8_t i = 0; i < CUBIES; ++i) {
        if (state->p[i] >= CUBIES || state->o[i] >= 3)
            return 0;
        for (uint8_t j = 0; j < i; ++j)
            if (state->p[j] == state->p[i])
                return 0;
        sum = (uint8_t) (sum + state->o[i]);
    }
    while (sum >= 3)
        sum = (uint8_t) (sum - 3);
    return sum == 0;
}

static int parse_state(const char *input, state_t *state)
{
    for (int i = 0; i < 7; ++i) {
        if (input[i] < '1' || input[i] > '7')
            return 0;
        state->p[i] = (uint8_t) (input[i] - '1');
    }
    for (int i = 0; i < 7; ++i) {
        if (input[i + 7] < '1' || input[i + 7] > '3')
            return 0;
        state->o[i] = (uint8_t) (input[i + 7] - '1');
    }
    return input[14] == '\0' && valid(state);
}

static void rank_state(const state_t *state, uint16_t *perm_rank,
                       uint16_t *ori_rank)
{
    uint32_t p;
    uint8_t smaller;

    smaller = 0;
    for (uint8_t j = 1; j < CUBIES; ++j)
        if (state->p[j] < state->p[0])
            ++smaller;
    p = smaller;

    smaller = 0;
    for (uint8_t j = 2; j < CUBIES; ++j)
        if (state->p[j] < state->p[1])
            ++smaller;
    p = (p << 2) + (p << 1) + smaller;

    smaller = 0;
    for (uint8_t j = 3; j < CUBIES; ++j)
        if (state->p[j] < state->p[2])
            ++smaller;
    p = (p << 2) + p + smaller;

    smaller = 0;
    for (uint8_t j = 4; j < CUBIES; ++j)
        if (state->p[j] < state->p[3])
            ++smaller;
    p = (p << 2) + smaller;

    smaller = 0;
    for (uint8_t j = 5; j < CUBIES; ++j)
        if (state->p[j] < state->p[4])
            ++smaller;
    p = (p << 1) + p + smaller;

    smaller = 0;
    if (state->p[6] < state->p[5])
        ++smaller;
    p = (p << 1) + smaller;

    uint32_t o = 0;
    for (uint8_t i = 0; i < 6; ++i)
        o = (o << 1) + o + state->o[i];

    *perm_rank = (uint16_t) p;
    *ori_rank = (uint16_t) o;
}

static uint8_t heuristic(uint16_t p, uint16_t o)
{
    uint8_t hp = perm_table[p], ho = ori_table[o];
    return hp > ho ? hp : ho;
}

static int ida_search(uint16_t start_perm, uint16_t start_ori,
                      uint8_t solution[MAX_DEPTH])
{
    frame_t stack[MAX_DEPTH + 1];
    uint8_t limit = heuristic(start_perm, start_ori);

    while (limit <= MAX_DEPTH) {
        uint8_t next_limit = UINT8_MAX;
        frame_t *top = stack;
        int depth = 0;

        top->perm = start_perm;
        top->ori = start_ori;
        top->move = NO_MOVE;
        top->next_move = 0;

        if (start_perm == 0 && start_ori == 0)
            return 0;

        while (1) {
            if (top->next_move >= 12) {
                if (top == stack)
                    break;
                --top;
                --depth;
                continue;
            }
            uint8_t move = top->next_move++;
            if ((move & 3U) == 3U)
                continue;

            uint8_t face = (uint8_t) (move >> 2U);
            if ((top->move >> 2U) == face)
                continue;

            uint16_t o = orientation[move][top->ori];
            uint16_t p = top->perm;

            uint8_t turns = (uint8_t) (move & 3U);
            for (uint8_t turn = 0; turn <= turns; ++turn)
                p = permutation[face][p];

            uint8_t f = (uint8_t) (depth + 1 + heuristic(p, o));
            if (f > limit) {
                if (f < next_limit)
                    next_limit = f;
                continue;
            }

            ++top;
            ++depth;
            top->perm = p;
            top->ori = o;
            top->move = move;
            top->next_move = 0;

            if (p == 0 && o == 0) {
                frame_t *ptr = stack + 1;
                for (int i = 0; i < depth; ++i, ++ptr) {
                    uint8_t m = ptr->move;
                    uint8_t f_move = m >> 2U;
                    solution[i] = (uint8_t) ((f_move << 1) + f_move + (m & 3U));
                }
                return depth;
            }
        }
        limit = next_limit;
    }
    return -1;
}

static int run(void)
{
    state_t state;
    uint8_t solution[MAX_DEPTH];

    if (!parse_state(INPUT, &state))
        return 2; /* invalid input, same as solver.c */

    uint16_t p, o;
    rank_state(&state, &p, &o);
    int length = ida_search(p, o, solution);

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
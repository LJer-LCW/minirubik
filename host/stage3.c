#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

enum {
    CUBIES = 7,
    PERMUTATIONS = 5040,
    ORIENTATIONS = 729,
    PERM_SIZE = 8192,
    ORI_SIZE = 1024,
    STATES = PERMUTATIONS * ORIENTATIONS,
    MOVES = 9,
    MAX_DEPTH = 11,
    NO_MOVE = 255
};

static uint16_t permutation[3][PERM_SIZE];
/* 12 rows for direct move-indexing: 
   Row 0..2 : R, R2, R'
   Row 4..6 : B, B2, B'
   Row 8..10: D, D2, D' 
*/
static uint16_t orientation[12][ORI_SIZE];

typedef struct {
    uint8_t p[CUBIES], o[CUBIES];
} state_t;

/*@ predicate valid_state(state_t *state) =
      (\forall integer i; 0 <= i < CUBIES ==>
         state->p[i] < CUBIES && state->o[i] < 3) &&
      (\forall integer i, j; 0 <= i < j < CUBIES ==>
         state->p[i] != state->p[j]) &&
      (state->o[0] + state->o[1] + state->o[2] + state->o[3] +
       state->o[4] + state->o[5] + state->o[6]) % 3 == 0;
 */

static const char *const move_names[MOVES] = {"R",  "R2", "R'", "B", "B2",
                                              "B'", "D",  "D2", "D'"};
static const uint8_t inverse_move[MOVES] = {2, 1, 0, 5, 4, 3, 8, 7, 6};
/* Each destination takes a cubie from source[face][destination]. */
static const uint8_t source[3][CUBIES] = {
    {1, 4, 2, 0, 3, 5, 6},
    {0, 1, 2, 4, 5, 6, 3},
    {0, 2, 5, 3, 1, 4, 6},
};
static const uint8_t twist[3][CUBIES] = {
    {1, 2, 0, 2, 1, 0, 0},
    {0, 0, 0, 1, 2, 1, 2},
    {0, 0, 0, 0, 0, 0, 0},
};

/* The three quarter-turns preserve the fixed front-upper-left corner. */
/*@ requires face < 3;
    assigns \nothing;
    ensures \forall integer i; 0 <= i < CUBIES ==>
              \result.p[i] == state.p[source[face][i]];
    ensures \forall integer i; 0 <= i < CUBIES ==>
              \result.o[i] == (state.o[source[face][i]] + twist[face][i]) % 3;
 */
static state_t quarter_turn(state_t state, uint8_t face)
{
    state_t result;
    /*@ loop invariant 0 <= i <= CUBIES;
        loop invariant \forall integer j; 0 <= j < i ==>
          result.p[j] == state.p[source[face][j]];
        loop invariant \forall integer j; 0 <= j < i ==>
          result.o[j] == (state.o[source[face][j]] + twist[face][j]) % 3;
        loop assigns i, result.p[0..6], result.o[0..6];
        loop variant CUBIES - i;
    */
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t from = source[face][i];
        result.p[i] = state.p[from];
        uint8_t o_sum = (uint8_t) (state.o[from] + twist[face][i]);
        while (o_sum >= 3)
            o_sum = (uint8_t) (o_sum - 3);
        result.o[i] = o_sum;
    }
    return result;
}

static state_t apply_move(state_t state, uint8_t move)
{
    uint8_t turns = (uint8_t) (move % 3U + 1U);
    for (uint8_t i = 0; i < turns; ++i)
        state = quarter_turn(state, (uint8_t) (move / 3U));
    return state;
}

/*@ requires \valid_read(state);
    requires \forall integer i; 0 <= i < CUBIES ==>
      0 <= state->p[i] < CUBIES;
    requires \forall integer i, j; 0 <= i < j < CUBIES ==>
      state->p[i] != state->p[j];
    requires \forall integer i; 0 <= i < CUBIES ==>
      0 <= state->o[i] < 3;
    assigns \nothing;
    ensures \result < STATES;
 */
static uint32_t rank_state(const state_t *state)
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

    return p * ORIENTATIONS + o;
}

/*@ requires \valid(state); requires rank < STATES; assigns *state; */
static void unrank_state(uint32_t rank, state_t *state)
{
    uint8_t available[CUBIES] = {0, 1, 2, 3, 4, 5, 6};
    uint32_t p = rank / ORIENTATIONS, o = rank % ORIENTATIONS, f = 720;
    uint8_t sum = 0;
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t q = (uint8_t) (p / f);
        p %= f;
        state->p[i] = available[q];
        for (uint8_t j = q; j + 1U < CUBIES - i; ++j)
            available[j] = available[j + 1U];
        if (i < 5)
            f /= 6U - i;
    }
    for (uint8_t i = 6; i-- > 0;) {
        state->o[i] = (uint8_t) (o % 3U);
        sum = (uint8_t) (sum + state->o[i]);
        o /= 3U;
    }
    while (sum >= 3)
        sum = (uint8_t) (sum - 3);
    state->o[6] = (uint8_t) ((3U - sum) % 3U);
}

/*@ requires \valid_read(state);
    requires \initialized(&state->p[0..6]) && \initialized(&state->o[0..6]);
    assigns \nothing;
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->p[i] < CUBIES && state->o[i] < 3;
    ensures \result != 0 ==> \forall integer i, j; 0 <= i < j < CUBIES ==>
      state->p[i] != state->p[j];
    ensures \result != 0 ==>
      (state->o[0] + state->o[1] + state->o[2] + state->o[3] +
       state->o[4] + state->o[5] + state->o[6]) % 3 == 0;
    ensures complete: valid_state(state) ==> \result != 0;
 */
static int valid(const state_t *state)
{
    uint8_t sum = 0;
    /*@ loop invariant 0 <= i <= CUBIES;
        loop invariant sum <= 2 * i;
        loop invariant \forall integer j; 0 <= j < i ==>
          state->p[j] < CUBIES && state->o[j] < 3;
        loop invariant \forall integer j, k; 0 <= j < k < i ==>
          state->p[j] != state->p[k];
        loop assigns i, sum;
        loop variant CUBIES - i;
    */
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

static void init_move_tables(void) {
    state_t state;
    for (uint16_t rank = 0; rank < PERMUTATIONS; ++rank) {
        unrank_state((uint32_t) rank * ORIENTATIONS, &state);
        for (uint8_t face = 0; face < 3; ++face) {
            state_t next = quarter_turn(state, face);
            permutation[face][rank] =
                (uint16_t) (rank_state(&next) / ORIENTATIONS);
        }
    }
    /* Build quarter-turn orientation tables (row 0, 4, 8) */
    for (uint16_t rank = 0; rank < ORIENTATIONS; ++rank) {
        unrank_state(rank, &state);
        for (uint8_t face = 0; face < 3; ++face) {
            state_t next = quarter_turn(state, face);
            orientation[face << 2][rank] =
                (uint16_t) (rank_state(&next) % ORIENTATIONS);
        }
    }
    /* Build half-turn and inverse orientation tables (rows 1,2 / 5,6 / 9,10) */
    for (uint8_t face = 0; face < 3; ++face) {
        uint8_t m0 = (uint8_t) (face << 2U);
        uint8_t m1 = (uint8_t) (m0 + 1U);
        uint8_t m2 = (uint8_t) (m0 + 2U);
        for (uint16_t rank = 0; rank < ORIENTATIONS; ++rank) {
            uint16_t o1 = orientation[m0][rank];
            orientation[m1][rank] = orientation[m0][o1];
            orientation[m2][rank] = orientation[m0][orientation[m1][rank]];
        }
    }
}

static uint8_t *build_perm_table(uint8_t *diameter)
{
    uint8_t *dist = malloc(PERMUTATIONS);
    uint16_t *queue = malloc(PERMUTATIONS * sizeof(*queue));
    uint16_t head = 0, tail = 1, level_end = 1;

    memset(dist, UINT8_MAX, PERMUTATIONS);
    queue[0] = 0;
    dist[0] = 0;
    *diameter = 0;

    while (head < tail) {
        if (head == level_end) {
            level_end = tail;
            ++*diameter;
        }
        uint16_t p = queue[head++];
        for (uint8_t face = 0; face < 3; ++face) {
            uint16_t next_p = p;
            for (uint8_t turn = 0; turn < 3; ++turn) {
                next_p = permutation[face][next_p];
                if (dist[next_p] == UINT8_MAX) {
                    dist[next_p] = *diameter + 1;
                    queue[tail++] = next_p;
                }
            }
        }
    }
    free(queue);
    return dist;
}

static uint8_t *build_ori_table(uint8_t *diameter)
{
    uint8_t *dist = malloc(ORIENTATIONS);
    uint16_t *queue = malloc(ORIENTATIONS * sizeof(*queue));
    uint16_t head = 0, tail = 1, level_end = 1;

    if (!dist || !queue) {
        free(dist);
        free(queue);
        return NULL;
    }

    memset(dist, UINT8_MAX, ORIENTATIONS);
    queue[0] = 0;
    dist[0] = 0;
    *diameter = 0;

    while (head < tail) {
        if (head == level_end) {
            level_end = tail;
            ++*diameter;
        }
        uint16_t o = queue[head++];
        for (uint8_t face = 0; face < 3; ++face) {
            uint16_t next_o = o;
            for (uint8_t turn = 0; turn < 3; ++turn) {
                next_o = orientation[face << 2U][next_o];
                if (dist[next_o] == UINT8_MAX) {
                    dist[next_o] = *diameter + 1;
                    queue[tail++] = next_o;
                }
            }
        }
    }
    free(queue);
    return dist;
}

static uint8_t *build_table(uint8_t *diameter)
{
    uint8_t *toward_solved = malloc(STATES);
    uint32_t *queue = malloc((size_t) STATES * sizeof *queue);
    
    uint32_t head = 0, tail = 1, level_end = 1;
    if (!toward_solved || !queue) {
        free(toward_solved);
        free(queue);
        return NULL;
    }

    memset(toward_solved, UINT8_MAX, STATES);
    queue[0] = 0;
    toward_solved[0] = 0;
    *diameter = 0;
    while (head < tail) {
        if (head == level_end) {
            level_end = tail;
            ++*diameter;
        }
        uint32_t here = queue[head++];
        uint16_t p = (uint16_t) (here / ORIENTATIONS);
        uint16_t o = (uint16_t) (here % ORIENTATIONS);
        for (uint8_t face = 0; face < 3; ++face) {
            uint16_t next_p = p, next_o = o;
            for (uint8_t turn = 0; turn < 3; ++turn) {
                next_p = permutation[face][next_p];
                next_o = orientation[face << 2U][next_o];
                uint32_t there = (uint32_t) next_p * ORIENTATIONS + next_o;
                if (toward_solved[there] == UINT8_MAX) {
                    toward_solved[there] = *diameter + 1;
                    queue[tail++] = there;
                }
            }
        }
    }
    free(queue);
    if (tail != STATES) {
        free(toward_solved);
        return NULL;
    }
    return toward_solved;
}

/* Parse state without modulo operators */
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

typedef struct {
    uint16_t perm;     
    uint16_t ori;      
    uint8_t move;      
    uint8_t next_move; 
} frame_t;

/* Heuristic: MAX(perm, ori) */
static uint8_t heuristic(const uint8_t *perm_table, const uint8_t *ori_table,
                         uint16_t p, uint16_t o)
{
    uint8_t hp = perm_table[p], ho = ori_table[o];
    return hp > ho ? hp : ho;
}

static int ida_search(uint16_t start_perm, uint16_t start_ori,
                      const uint8_t *perm_table, const uint8_t *ori_table,
                      uint8_t solution[MAX_DEPTH], uint64_t *nodes)
{
    frame_t stack[MAX_DEPTH + 1];
    uint8_t limit = heuristic(perm_table, ori_table, start_perm, start_ori);
    *nodes = 0;

    while (limit <= MAX_DEPTH) {
        uint8_t next_limit = UINT8_MAX;
        frame_t *top = stack;
        int depth = 0;

        top->perm = start_perm;
        top->ori = start_ori;
        top->move = NO_MOVE;
        top->next_move = 0;
        ++*nodes;

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
            if ((top->move >> 2U) == face) continue;

            uint16_t o = orientation[move][top->ori];
            uint16_t p = top->perm;
            
            uint8_t turns = (uint8_t) (move & 3U);
            for (uint8_t turn = 0; turn <= turns; ++turn) {
                p = permutation[face][p];
            }

            uint8_t f = (uint8_t) (depth + 1 +
                                   heuristic(perm_table, ori_table, p, o));
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
            ++*nodes;

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

int main(void)
{
    init_move_tables();

    uint8_t full_diameter;
    uint8_t *full_table = build_table(&full_diameter);
    if (!full_table) {
        fputs("could not build complete state table\n", stderr);
        return 1;
    }

    uint32_t full_counts[12] = {0}; 
    uint64_t full_sum = 0; 
    for (uint32_t i = 0; i < STATES; ++i) {
        uint8_t d = full_table[i];
        if (d <= 11) {
            full_counts[d]++;
            full_sum += d;
        }
    }

    puts("=== Full State Distance Distribution ===");
    for (int i = 0; i <= full_diameter; ++i) {
        printf("Distance %2d: %7u states\n", i, full_counts[i]);
    }
    printf("Full Max distance (Diameter): %d\n", full_diameter);
    double full_avg = (double)full_sum / STATES;
    printf("Full Average distance: %.3f\n\n", full_avg);

    uint8_t perm_diameter;
    uint8_t *perm_table = build_perm_table(&perm_diameter);
    if (!perm_table) {
        fputs("Failed to build perm table\n", stderr);
        free(full_table);
        return 1;
    }

    uint32_t perm_counts[12] = {0}; 
    uint64_t perm_sum = 0; 
    for (uint32_t i = 0; i < PERMUTATIONS; ++i) {
        uint8_t d = perm_table[i];
        if (d < 12) {
            perm_counts[d]++;
            perm_sum += d;
        }
    }

    puts("=== Permutation Distance Distribution ===");
    for (int i = 0; i <= perm_diameter; ++i) {
        printf("Distance %2d: %7u states\n", i, perm_counts[i]);
    }
    printf("Permutation Max distance (Diameter): %d\n", perm_diameter);
    double perm_avg = (double)perm_sum / PERMUTATIONS;
    printf("Permutation Average distance: %.3f\n", perm_avg);
    printf("Average Underestimate (Gap): %.3f steps\n\n", full_avg - perm_avg);

    int h1_passed = 1; 
    for (uint32_t rank = 0; rank < STATES; ++rank) {
        uint8_t true_d = full_table[rank];
        uint16_t perm_rank = (uint16_t)(rank / ORIENTATIONS);
        uint8_t h_val = perm_table[perm_rank];

        if (h_val > true_d) {
            printf("H1 Check FAILED at rank %u: h(%u) = %u > true_d = %u\n", 
                   rank, perm_rank, h_val, true_d);
            h1_passed = 0; 
            break;
        }
    }

    if (h1_passed) {
        puts("=== Gate H1 Check PASSED: h(s) <= d(s) for all 3,674,160 states ===");
    }

    uint8_t ori_diameter;
    uint8_t *ori_table = build_ori_table(&ori_diameter);

    if (!ori_table) {
        fputs("Failed to build ori table\n", stderr);
        free(perm_table);
        free(full_table);
        return 1;
    }

    uint32_t ori_counts[12] = {0}; 
    uint64_t ori_sum = 0;

    for (uint32_t i = 0; i < ORIENTATIONS; ++i) { 
        uint8_t d = ori_table[i];
        if (d < 12) {
            ori_counts[d]++;
            ori_sum += d;
        }
    }
    puts("=== Orientation Distance Distribution ===");
    for (int i = 0; i <= ori_diameter; ++i) {
        printf("Distance %2d: %7u states\n", i, ori_counts[i]);
    }

    printf("Orientation Max distance (Diameter): %d\n", ori_diameter);
    double ori_avg = (double)ori_sum / ORIENTATIONS;
    printf("Orientation Average distance: %.3f\n\n", ori_avg);

    int ori_h1_passed = 1;
    int max_h1_passed = 1;
    int sum_h1_passed = 1;
    
    uint64_t max_sum = 0; 

    for (uint32_t rank = 0; rank < STATES; ++rank) {
        uint8_t true_d = full_table[rank];
        
        uint16_t perm_rank = (uint16_t)(rank / ORIENTATIONS);
        uint16_t ori_rank = (uint16_t)(rank % ORIENTATIONS);
        
        uint8_t h_perm = perm_table[perm_rank];
        uint8_t h_ori = ori_table[ori_rank];
        
        uint8_t h_max = (h_perm > h_ori) ? h_perm : h_ori;
        uint8_t h_sum = h_perm + h_ori;
        
        max_sum += h_max;

        if (h_ori > true_d && ori_h1_passed) {
            printf("Orientation H1 FAILED at rank %u: h_ori(%u) = %u > true_d(%u)\n", 
                   rank, ori_rank, h_ori, true_d);
            ori_h1_passed = 0;
        }
        
        if (h_max > true_d && max_h1_passed) {
            printf("MAX H1 FAILED at rank %u\n", rank);
            max_h1_passed = 0;
        }
        
        if (h_sum > true_d && sum_h1_passed) {
            printf("SUM H1 FAILED at rank %u: h_perm(%u) + h_ori(%u) = %u > true_d = %u\n", 
                   rank, h_perm, h_ori, h_sum, true_d);
            sum_h1_passed = 0;
        }
    }

    if (ori_h1_passed) puts("=== Orientation H1 Check PASSED ===");
    
    if (max_h1_passed) {
        puts("=== MAX(perm, ori) H1 Check PASSED ===");
        printf("MAX Average distance: %.3f\n", (double)max_sum / STATES);
    }
    
    if (sum_h1_passed) {
        puts("=== SUM(perm, ori) H1 Check PASSED ===");
    } else {
        puts("=== SUM(perm, ori) H1 Check FAILED (As expected: Not Admissible) ===");
    }

    puts("\n=== Testing IDA* Search ===");
    {
        const state_t solved = {{0, 1, 2, 3, 4, 5, 6}, {0}};
        state_t tests[3];
        const char *names[3] = {"Solved state", "One R move",
                                "Input 21345671111111"};
        const int expected[3] = {0, 1, 11};

        tests[0] = solved;
        tests[1] = apply_move(solved, 0); 
        if (!parse_state("21345671111111", &tests[2])) {
            puts("ERROR: cannot parse 21345671111111");
            return 1;
        }

        for (int t = 0; t < 3; ++t) {
            uint32_t rank = rank_state(&tests[t]);
            uint8_t solution[MAX_DEPTH];
            uint64_t nodes = 0;
            int length = ida_search((uint16_t) (rank / ORIENTATIONS),
                                    (uint16_t) (rank % ORIENTATIONS),
                                    perm_table, ori_table, solution, &nodes);

            printf("Test %d: %s (rank %u)\n", t + 1, names[t], rank);
            printf("  Nodes: %llu\n", (unsigned long long) nodes);
            printf("  Steps: %d (expected %d)\n", length, expected[t]);
            printf("  Solution:");
            for (int i = 0; i < length; ++i)
                printf(" %s", move_names[solution[i]]);
            puts("");

            state_t replay = tests[t];
            for (int i = 0; i < length; ++i)
                replay = apply_move(replay, solution[i]);
            if (length != expected[t] || memcmp(&replay, &solved, sizeof solved)) {
                puts("  ERROR: wrong length or solution does not reach solved");
                return 1;
            }
        }
    }

    {
        uint32_t bad = 0;
        for (uint32_t rank = 0; rank < STATES; ++rank) {
            state_t state;
            unrank_state(rank, &state);
            uint32_t back = rank_state(&state);
            if (back != rank) {
                if (bad < 5)
                    printf("RANK ERROR: rank %u came back as %u\n", rank, back);
                ++bad;
            }
        }
        if (bad) {
            printf("=== Rank round-trip FAILED: %u mismatches ===\n", bad);
            return 1;
        }
        printf("\n=== Rank round-trip PASSED for all %u states ===\n",
               (unsigned) STATES);
    }
   
      /* === Gate H3: IDA* length equals BFS distance across ALL STATES === */
    /*{
        uint64_t h3_total = 0;
        uint64_t h3_max = 0;
        uint32_t h3_max_rank = 0;
        uint32_t h3_count = 0;

        for (uint32_t rank = 0; rank < STATES; ++rank) {
            uint16_t test_p = (uint16_t)(rank / ORIENTATIONS);
            uint16_t test_o = (uint16_t)(rank % ORIENTATIONS);

            uint8_t test_solution[MAX_DEPTH];
            uint64_t test_nodes = 0;
            int test_length = ida_search(test_p, test_o, perm_table, ori_table, test_solution, &test_nodes);

            if (test_length != full_table[rank]) {
                printf("H3 ERROR: rank %u returned %d, expected %u\n",
                       rank, test_length, full_table[rank]);
                return 1;
            }

            h3_count++;
            h3_total += test_nodes;

            if (test_nodes > h3_max) {
                h3_max = test_nodes;
                h3_max_rank = rank;
            }
        }

        printf("\n=== Gate H3: IDA* length equals BFS distance ===\n");
        printf("States checked: %u\n", h3_count);
        printf("Total nodes: %llu\n", (unsigned long long) h3_total);
        printf("Maximum nodes: %llu (rank %u)\n", (unsigned long long) h3_max, h3_max_rank);
        puts("=== Gate H3 PASSED ===");
    }*/

    /* Statistics over all distance-11 states */
    clock_t start_time = clock();

    uint64_t min_nodes = UINT64_MAX;
    uint64_t max_nodes = 0;
    uint64_t total_nodes = 0;
    uint32_t min_rank = 0;
    uint32_t max_rank = 0;
    uint32_t count = 0;

    for (uint32_t rank = 0; rank < STATES; ++rank) {
        if (full_table[rank] != 11) continue;

        uint16_t test_p = (uint16_t)(rank / ORIENTATIONS);
        uint16_t test_o = (uint16_t)(rank % ORIENTATIONS);

        uint8_t test_solution[MAX_DEPTH];
        uint64_t test_nodes = 0;
        int test_length = ida_search(test_p, test_o, perm_table, ori_table, test_solution, &test_nodes);

        if (test_length != 11) {
            printf("ERROR: rank %u returned length %d\n", rank, test_length);
            return 1;
        }
        count++;
        total_nodes += test_nodes;
        
        if (test_nodes < min_nodes) {
            min_nodes = test_nodes;
            min_rank = rank;
        }

        if (test_nodes > max_nodes) {
            max_nodes = test_nodes;
            max_rank = rank;
        }
    }

    clock_t end_time = clock();
    double elapsed_sec = (double)(end_time - start_time) / CLOCKS_PER_SEC;
    double average_nodes = (double)total_nodes / count;

    printf("\n=== Distance-11 IDA* Statistics ===\n");
    printf("Distance-11 states benchmarked: %u\n", count);
    printf("Total Execution Time: %.2f seconds\n", elapsed_sec);
    printf("Minimum nodes: %llu (rank %u)\n", (unsigned long long)min_nodes, min_rank);
    printf("Maximum nodes: %llu (rank %u)\n", (unsigned long long)max_nodes, max_rank);
    printf("Average nodes: %.3f\n", average_nodes);
    printf("Total nodes searched: %llu\n", (unsigned long long)total_nodes);
    if (elapsed_sec > 0) {
        printf("Search Speed: %.0f nodes/sec\n", (double)total_nodes / elapsed_sec);
    }

    free(ori_table);
    free(perm_table);
    free(full_table);

    return 0;
}
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>


enum {
    CUBIES = 7,
    PERMUTATIONS = 5040,
    ORIENTATIONS = 729,
    STATES = PERMUTATIONS * ORIENTATIONS,
    MOVES = 9
};

static uint16_t permutation[3][PERMUTATIONS];
static uint16_t orientation[3][ORIENTATIONS];


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
        result.o[i] = (uint8_t) ((state.o[from] + twist[face][i]) % 3U);
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
    uint32_t p = 0, o = 0;
    /*@ loop invariant 0 <= i <= CUBIES;
        loop invariant (i == 0 ==> p == 0) && (i == 1 ==> p <= 6) &&
          (i == 2 ==> p <= 41) && (i == 3 ==> p <= 209) &&
          (i == 4 ==> p <= 839) && (i == 5 ==> p <= 2519) &&
          (i >= 6 ==> p <= 5039);
        loop assigns i, p;
        loop variant CUBIES - i;
     */
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t smaller = 0;
        /*@ loop invariant i + 1 <= j <= CUBIES;
            loop invariant smaller <= j - i - 1;
            loop assigns j, smaller;
            loop variant CUBIES - j;
         */
        for (uint8_t j = (uint8_t) (i + 1U); j < CUBIES; ++j)
            if (state->p[j] < state->p[i])
                ++smaller;
        p = p * (CUBIES - i) + smaller;
    }
    /*@ loop invariant 0 <= i <= 6;
        loop invariant (i == 0 ==> o == 0) && (i == 1 ==> o < 3) &&
          (i == 2 ==> o < 9) && (i == 3 ==> o < 27) &&
          (i == 4 ==> o < 81) && (i == 5 ==> o < 243) &&
          (i == 6 ==> o < 729);
        loop assigns i, o;
        loop variant 6 - i;
     */
    for (uint8_t i = 0; i < 6; ++i)
        o = o * 3U + state->o[i];
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
    state->o[6] = (uint8_t) ((3U - sum % 3U) % 3U);
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
        loop invariant sum == (i > 0 ? state->o[0] : 0) +
          (i > 1 ? state->o[1] : 0) + (i > 2 ? state->o[2] : 0) +
          (i > 3 ? state->o[3] : 0) + (i > 4 ? state->o[4] : 0) +
          (i > 5 ? state->o[5] : 0) + (i > 6 ? state->o[6] : 0);
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
        /*@ loop invariant 0 <= j <= i;
            loop invariant \forall integer k; 0 <= k < j ==>
              state->p[k] != state->p[i];
            loop assigns j;
            loop variant i - j;
        */
        for (uint8_t j = 0; j < i; ++j)
            if (state->p[j] == state->p[i])
                return 0;
        sum = (uint8_t) (sum + state->o[i]);
    }
    return sum % 3U == 0;
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
    for (uint16_t rank = 0; rank < ORIENTATIONS; ++rank) {
        unrank_state(rank, &state);
        for (uint8_t face = 0; face < 3; ++face) {
            state_t next = quarter_turn(state, face);
            orientation[face][rank] =
                (uint16_t) (rank_state(&next) % ORIENTATIONS);
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
                next_o = orientation[face][next_o];
                
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
                next_o = orientation[face][next_o];
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

/*@ requires valid_read_string(input);
    requires \valid(state);
    assigns state->p[0..6], state->o[0..6];
    ensures \result != 0 ==> input[14] == '\0';
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->p[i] < CUBIES && state->o[i] < 3;
    ensures \result != 0 ==> \forall integer i, j; 0 <= i < j < CUBIES ==>
      state->p[i] != state->p[j];
    ensures \result != 0 ==>
      (state->o[0] + state->o[1] + state->o[2] + state->o[3] +
       state->o[4] + state->o[5] + state->o[6]) % 3 == 0;
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->p[i] == input[i] - '1';
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->o[i] == input[i + CUBIES] - '1';
 */
static int parse_state(const char *input, state_t *state)
{
    /*@ loop invariant 0 <= i <= 14;
        loop invariant i <= strlen(input);
        loop invariant i <= 7 ==> \initialized(&state->p[0..i-1]);
        loop invariant i >= 7 ==> \initialized(&state->p[0..6]);
        loop invariant i >= 7 ==> \initialized(&state->o[0..i-8]);
        loop invariant \forall integer j; 0 <= j < i && j < CUBIES ==>
          state->p[j] == input[j] - '1';
        loop invariant \forall integer j; 0 <= j < i - CUBIES ==>
          state->o[j] == input[j + CUBIES] - '1';
        loop assigns i, state->p[0..6], state->o[0..6];
        loop variant 14 - i;
     */
    for (int i = 0; i < 14; ++i) {
        int limit = i < 7 ? 7 : 3;
        if (input[i] < '1' || input[i] > '0' + limit)
            return 0;
        (i < 7 ? state->p : state->o)[i % 7] = (uint8_t) (input[i] - '1');
    }
    return input[14] == '\0' && valid(state);
}

static int output_failed(void)
{
    return fflush(stdout) != 0 || ferror(stdout);
}

static int self_test(void)
{
    const state_t solved = {{0, 1, 2, 3, 4, 5, 6}, {0}};
    state_t state;
    for (uint8_t move = 0; move < MOVES; ++move) {
        state = solved;
        state = apply_move(state, move);
        state = apply_move(state, inverse_move[move]);
        if (memcmp(&solved, &state, sizeof solved))
            return 0;
    }
    for (uint32_t rank = 0; rank < STATES; ++rank) {
        unrank_state(rank, &state);
        if (!valid(&state) || rank_state(&state) != rank)
            return 0;
    }
    return 1;
}

enum { MAX_DEPTH = 11, NO_MOVE = 255 };

typedef struct {
    uint16_t perm;     
    uint16_t ori;      
    uint8_t move;      
    uint8_t next_move; 
} frame_t;

static uint8_t heuristic(const uint8_t *perm_table, const uint8_t *ori_table,
                         uint16_t p, uint16_t o)
{
    uint8_t hp = perm_table[p], ho = ori_table[o];
    return hp > ho ? hp : ho;
}

//power-of-two
static int ida_search(uint16_t start_perm, uint16_t start_ori,
                      const uint8_t *perm_table, const uint8_t *ori_table,
                      uint8_t solution[MAX_DEPTH], uint64_t *nodes)
{
    frame_t stack[MAX_DEPTH + 1];
    uint8_t limit = heuristic(perm_table, ori_table, start_perm, start_ori);
    *nodes = 0;

    while (limit <= MAX_DEPTH) {
        uint8_t next_limit = UINT8_MAX;
        int top = 0;
        stack[0].perm = start_perm;
        stack[0].ori = start_ori;
        stack[0].move = NO_MOVE;
        stack[0].next_move = 0;
        ++*nodes;
        if (start_perm == 0 && start_ori == 0)
            return 0;

        while (top >= 0) {
            frame_t *node = &stack[top];
            if (node->next_move >= 12) { 
                --top;
                continue;
            }
            uint8_t move = node->next_move++;
            if ((move & 3U) == 3U)
                continue;

            uint8_t face = (uint8_t) (move >> 2U);
            if (node->move != NO_MOVE && (node->move >> 2U) == face)
                continue; 

            uint16_t p = node->perm, o = node->ori;
            uint8_t turns = (uint8_t) (move & 3U);
            for (uint8_t turn = 0; turn <= turns; ++turn) {
                p = permutation[face][p];
                o = orientation[face][o];
            }

            uint8_t f = (uint8_t) (top + 1 +
                                   heuristic(perm_table, ori_table, p, o));
            if (f > limit) {
                if (f < next_limit)
                    next_limit = f;
                continue;
            }

            ++top;
            stack[top].perm = p;
            stack[top].ori = o;
            stack[top].move = move;
            stack[top].next_move = 0;
            ++*nodes;
            if (p == 0 && o == 0) {
                for (int i = 1; i <= top; ++i) {
                    uint8_t m = stack[i].move;
                    solution[i - 1] = (uint8_t) ((m >> 2U) * 3U + (m & 3U));
                }
                return top;
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

    double average_nodes = (double)total_nodes / count;
    printf("\n=== Distance-11 IDA* Statistics ===\n");
    printf("Distance-11 states: %u\n", count);
    printf("Minimum nodes: %llu (rank %u)\n", (unsigned long long)min_nodes, min_rank);
    printf("Maximum nodes: %llu (rank %u)\n", (unsigned long long)max_nodes, max_rank);
    printf("Average nodes: %.3f\n", average_nodes);

    /*
    {
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
    }
    */

    free(ori_table);
    free(perm_table);
    free(full_table);

    return 0;
}
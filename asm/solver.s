.data
msg: .string "@INPUT@"

state_perm: .zero 7
state_ori: .zero 7

.text
main:
    j parse_state_setup


rank_state:
    la t3, state_perm # get state_perm start addr.
    li a3, 7 # loop upper limit
    li t0, 0 # permutation rank p

    lbu t4, 0(t3) # state_perm[0]
    li t1, 1 # j = 1
    add t2, t1, t3 #  state_perm[1] addr.
    li t6, 0 # smaller = 0

rank_p0_loop:

    bge t1, a3, rank_p0_done # for loop (i<6) == (i<= 7)
    lbu t5, 0(t2) # state_perm[j] 
    bgeu t5, t4, rank_p0_next # if  state_perm[j]  >= state_perm[0],go to p[0] next
    addi t6, t6, 1 # smaller++

rank_p0_next:

    addi t1, t1, 1 
    addi t2, t2, 1
    j rank_p0_loop

rank_p0_done:

    addi t0, t6, 0 #p = smaller

    lbu t4, 1(t3) # state_perm[1]
    li t1, 2 # j = 2
    add t2, t1, t3 #  state_perm[2] addr. 
    li t6, 0 

rank_p1_loop:

    bge t1, a3, rank_p1_done
    lbu t5, 0(t2)
    bgeu t5, t4, rank_p1_next
    addi t6, t6, 1

rank_p1_next:

    addi t1, t1, 1
    addi t2, t2, 1
    j rank_p1_loop

rank_p1_done:

    slli t4, t0, 2 # t4 = t0<<2 = 4t0= 4p
    slli t5, t0, 1 # t5 = t0<<1 = 2p
    add t4, t4, t5 #t4 = 6p now
    add t0, t4, t6 # c code : p=p *6 + smaller

    lbu t4, 2(t3) # state_perm[2]
    li t1, 3 #t1 = 3
    add t2, t1, t3 
    li t6, 0

rank_p2_loop:

    bge t1, a3, rank_p2_done
    lbu t5, 0(t2)
    bgeu t5, t4, rank_p2_next
    addi t6, t6, 1

rank_p2_next:

    addi t1, t1, 1
    addi t2, t2, 1
    j rank_p2_loop

rank_p2_done:

    slli t4, t0, 2 # (p<<2)
    add t4, t4, t0 # (p<<2) +p
    add t0, t4, t6 # (p<<2) +p + smaller

    lbu t4, 3(t3)
    li t1, 4
    add t2, t3, t1
    li t6, 0

rank_p3_loop:

    bge t1, a3, rank_p3_done
    lbu t5, 0(t2)
    bgeu t5, t4, rank_p3_next
    addi t6, t6, 1

rank_p3_next:
    addi t1, t1, 1
    addi t2, t2, 1
    j rank_p3_loop

rank_p3_done:
    slli t4, t0, 2
    add t0, t4, t6

    lbu t4, 4(t3)
    li t1, 5
    add t2, t3, t1
    li t6, 0


rank_p4_loop:
    bge t1, a3, rank_p4_done
    lbu t5, 0(t2)
    bgeu t5, t4, rank_p4_next
    addi t6, t6, 1

rank_p4_next:
    addi t1, t1, 1
    addi t2, t2, 1
    j rank_p4_loop
rank_p4_done:
    slli t4, t0, 1
    add t4, t4, t0
    add t0, t4, t6

    lbu t4, 5(t3)
    li t1, 6
    add t2, t3, t1
    li t6, 0


rank_p5_loop:
    bge t1, a3, rank_p5_done
    lbu t5, 0(t2)
    bgeu t5, t4, rank_p5_next
    addi t6, t6, 1
rank_p5_next:
    addi t1, t1, 1
    addi t2, t2, 1
    j rank_p5_loop
rank_p5_done:
    slli t4, t0, 1
    add t0, t4, t6
    addi a0, t0, 0 # a0 = permutation rank

    la t2, state_ori
    li t0, 0 # orientation rank
    li t1, 0 # i
    li t6, 6 # use only the first six orientations

    
rank_ori_loop:
# c code : o = (o << 1) + o + state->o[i];
    bge t1, t6, rank_ori_done
    add t3, t2, t1
    lbu t4, 0(t3)
    slli t5, t0, 1
    add t0, t0, t5
    add t0, t0, t4
    addi t1, t1, 1
    j rank_ori_loop
rank_ori_done:
    addi a1, t0, 0 # a1 = orientation rank
    ret

parse_state_setup:

	li t0, 0 # t0 for loop i = 0
    li t1, 7 # t1 for loop upper limit
    la t2, msg # t2 is string start addr. 
    la t3, state_perm # t3 is  array start addr.







parse_state_perm:

    bge t0, t1, parse_state_ori_setup
    add t4, t0, t2 # string start addr + i
    lbu t5, 0(t4) # load current string address 

    li t6, 49 # '1''s ASCII code 
	bltu t5, t6, wrong_input
    li t6, 56 # '7''s ASCII code 
    bgeu t5, t6, wrong_input

    add t4, t0, t3 # get array addr state->p[i]
    addi t5, t5, -49 # C code : input[i] - '1'
    sb t5, 0(t4) # C code : state->p[i]

    addi t0,t0, 1
    j parse_state_perm

parse_state_ori_setup:
    li t0, 0 # t0 for loop i = 0
    la t3, state_ori # t3 is  array start addr.

parse_state_ori:

    bge t0, t1, check_input
    addi t4, t0, 7 # offset = i+7
    add t4, t2, t4 # t4 = input + offset
    lbu t5, 0(t4) # load current string address 

    li t6, 49 # '1''s ASCII code 
	bltu t5, t6, wrong_input
    li t6, 52 # '4''s ASCII code 
    bgeu t5, t6, wrong_input

    addi t5, t5, -49 # convert '1'to '3' -> '0' to '2'
    add t4, t3, t0 #  get array addr state->o[i]
    sb t5, 0(t4) # state->o[i]

    addi t0,t0, 1
    j parse_state_ori

check_input:
   
    addi t4, t2, 14 # addr. string +14
    lbu t5, 0(t4) #input[14]
    bnez t5, wrong_input  # input[14] != '\0'

    jal ra, valid
    beqz a0, wrong_input # valid(state) = 0

    jal ra, rank_state
    mv s0, a1 # preserve orientation rank
    mv a0, s0
    li a7, 1
    ecall
    j exit_loop

valid:
    li t0, 0 # seen mask
    li t1, 1 # bit base
    li t3, 0 # i
    li t6, 7 # number of cubies
    la t2, state_perm
valid_perm_loop:
    bge t3, t6, valid_ori_setup
    add t4, t2, t3
    lbu t4, 0(t4) # p[i]
    sll t5, t1, t4 # mask = 1 << p[i]
    and t4, t0, t5
    bnez t4, invalid # already seen
    or t0, t0, t5 # mark p[i] as seen
    addi t3, t3, 1
    j valid_perm_loop

valid_ori_setup:
    li t0, 0 # sum = 0
    li t1, 0 # i = 0
    la t2, state_ori
CUBIES_loop: 
    bge t1, t6, valid_CUBIES_loop_setup # i>=CUBIES, exit
    add t3, t1, t2 # addr. of state->o[i]
    lbu t4, 0(t3) # state->o[i]
    add t0, t0, t4 # sum + state->o[i]
    addi t1, t1, 1 # ++i
    j CUBIES_loop
valid_CUBIES_loop_setup:
    li t5, 3
valid_while_sum:
    bltu t0, t5, valid_sum_check # branch if sum is less than 3
    addi t0, t0, -3 # sum-=3
    j valid_while_sum
valid_sum_check:
    bnez t0, invalid #branch if  sum!=0
    li a0, 1
    ret

invalid:
    li a0, 0
    ret





exit_loop: 
    
    li a0, 0 # return 0
    li a7, 93
    ecall

wrong_input:

    li a0, 2 # return 2 if the input is wrong
    li a7, 93
    ecall
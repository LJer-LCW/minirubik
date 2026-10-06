.data
msg: .string "@INPUT@"

state_perm: .zero 7
state_ori: .zero 7

.text
main:
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

    j exit_loop

valid:


exit_loop: 
    
    li a0, 0 # return 0
    li a7, 93
    ecall

wrong_input:

    li a0, 2 # return 2 if the input is wrong
    li a7, 93
    ecall
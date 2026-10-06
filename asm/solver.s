.data
msg: .string "@INPUT@"

state_perm: .zero 7
state_ori: .zero 7
ida_stack: .zero 72
solution: .zero 11

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

    bge t1, a3, rank_p0_done # for loop (j<=6) == (j< 7)
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
    la s5, ida_stack # stack base
    sh a0, 0(s5) # root frame perm
    sh a1, 2(s5) # root frame ori
    
    bnez a0, root_not_solved
    bnez a1, root_not_solved
    li s9, 0   # solved, so step is 0
    j found

root_not_solved:



    # The s registers are to prevent the value be over written.
    mv s1, a0 # perm rank in a0
    mv s0, a1 # ori rank in a1 

    # IDA* 
    # s0 = permutation base
    # s1 = perm_table base
    # s2 = orientation base
    # s3 = constant 3
    # s4 = ori_table base
    # s5 = ida stack base
    # s6 = limit
    # s7 = next_limit
    # s8 = top
    # s9 = depth
    # s10 = solution base
    # s11 = constant 12
    # Temps: t0=move, t1=face, t2=turns, t3=p, t4=o, t5=h, t6=f, a1=address
    # Extra : a2-a6
    

    # Frame layout (6 bytes per frame):
    # offset  size(bytes)  field       load/store
    # 0       2             perm        lhu / sh
    # 2       2             ori         lhu / sh
    # 4       1             move        lbu / sb
    # 5       1             next_move   lbu / sb
    


    # heuristic 
    #  IDA* setup
    la s0, permutation # s0 = permutation base
    la s1, perm_table # s1 = perm_table base
    la s2, orientation # s2 = orientation base
    li s3, 3 # s3 = constant 3
    la s4 , ori_table # s4 = ori_table base
    la s5, ida_stack # s5 = stack base
    la s10, solution # s10 = solution base
    li s11, 12 # s11 = constant 12

    # set root = NO_MOVE
    li t0, 255
    sb t0, 4(s5) # move is 1 byte, and  its offset is 4

    # limit = max(perm_table[p], ori_table[o])
    lhu t3, 0(s5) # root perm rank size is 2 byte, so lhu
    add a1, s1, t3 # perm_table[p] addr.
    lbu t5, 0(a1) # hp = perm_table[p]

    lhu t4, 2(s5)  # ori offset : 2-3, 2 bytes
    add a1, s4, t4
    lbu t6, 0(a1) 

    bltu t5, t6, ida_limit_use_ho
    mv s6, t5
    j IDA_loop_start
ida_limit_use_ho:
    mv s6, t6

IDA_loop_start:
    li s7, 255   # next_limit max. 8 bit max is 255
    mv s8, s5    # top = stack base
    li s9, 0   # depth = 0
    li t0, 0
    sb t0, 5(s5)  # root next_move = 0

IDA_inner_loop:
    lbu t0, 5(s8)  # read top->next_move, next_move offset 5, and its size is 1 byte
    bgeu t0, s11, IDA_moves_done #if next_move >= 12, branch to ida_moves_done.

    #  next_move++, next round
    addi a2, t0, 1
    sb a2, 5(s8) # next_move++

    andi t2, t0, 3 # turns = move & 3
    li t3, 3 # t3 = 3
    beq t2, t3, IDA_inner_loop # turns==3 is not a valid move 

    srli t1, t0, 2   # face = move >> 2
    lbu t3, 4(s8) # read current frame's move (move offset : 4 , 1 byte)
    srli t3, t3, 2    # prev_face = prev move >> 2
    beq t1, t3, IDA_inner_loop  # c: same face shows up continuously, skip

    # read orientation[move][top->ori]

    lhu t3, 2(s8) # t3 = top->ori, ori at offset 2-3, 2 bytes , so lhu
    # move * 2048 bytes, each move is corresponding to 1 row
    # and each row has 1024 entries, and each is 2 bytes (uint16_t), 2048 = 2^11
    slli t5, t0, 11        
    slli t6, t3, 1  # ori * 2 bytes (uint16_t), ori*2 = ori << 1
    add a1, s2, t5  # orientation base + move row offset
    add a1, a1, t6  # + ori offset
    lhu t4, 0(a1)   # t4 = orientation[move][top->ori]

    lhu t3, 0(s8) # top->perm , perm offset is 0, 2 bytes
    
    # permutation[face] 
    # each face has 8192 uint16_t entries, each entry has 2 bytes. 8192*2=16384=2^14
    slli a2, t1, 14 
    add a2, a2, s0 # permutation[face] addr.

    li t6, 0 # turn = 0

perm_turn_loop:
    bltu t2, t6, perm_turn_done  # end when turn > turns

    slli t5, t3, 1  # p * 2, each permutation entries is 2 bytes ( uint16_t )
    add a1, a2, t5 # permutation[face][p] addr.
    lhu t3, 0(a1) # p = permutation[face][p] (lh : 2 bytes)

    addi t6, t6, 1 # ++turn
    j perm_turn_loop

perm_turn_done:
    add a1, s1, t3 # perm_table + p addr.
    lbu t5 , 0(a1) # hp = perm_table[p]

    add a1, s4, t4 # ori_table + o addr.
    lbu t6 , 0(a1) # ho = ori_table[o]

    bltu t5, t6, heuristic_max_done # if hp <ho, t6 is larger.
    mv t6, t5 # else, t6=hp

heuristic_max_done:

    addi t5, s9, 1 # depth +1
    add t6, t6, t5 #depth+1+max(hp, ho)

    bltu s6, t6, IDA_path_e # if limit < f , go path e
    j IDA_path_f # else f <= limit , go path f 

IDA_path_e:
    bgeu t6, s7, IDA_inner_loop # if f>= next_limit, no update
    mv s7, t6 # next_limit = f
    j IDA_inner_loop

IDA_path_f:
    addi s8, s8, 6 # top+6
    addi s9, s9, 1 # depth +1

    sh t3, 0(s8) # child.perm = p (offset 0, 2 bytes)
    sh t4, 2(s8) # child.ori = o (offset 2, 2 bytes)
    sb t0, 4(s8) # child.move = move (offset 4, 1 byte)
    sb x0, 5(s8) # child.next_move = 0

    bnez t3, child_not_solved
    bnez t4, child_not_solved
    j found  # p == 0 and  o == 0

child_not_solved:
    j IDA_inner_loop

found:
    addi a2, s5, 6 # a2 = stack[1] (frame size = 6 byte)
    li a3, 0 # initialize index

print_solution_loop:
    bgeu a3, s9, print_solution_done # if output depth number of move, end loop
    lbu t0, 4(a2)  # read frame.move (offset 4, 1 byte)
    srli t1, t0, 2  # face = move >> 2
    andi t2, t0, 3   # turn = move & 3

    li t3, 82   # 'R' ASCII
    beq t1, x0, print_face
    li t3, 66   # 'B' ASCII
    li t4, 1 # t4 = 1
    beq t1, t4, print_face
    li t3, 68   # 'D' ASCII 

print_face:

    mv a0, t3 # move ASCII in t3 to a0
    li a7, 11 # sys. call, print single char
    ecall

    beq t2, x0, print_move_done # t2 is turn, if turn == 0, no suffix
    li t3, 50   # 2 in ASCII
    li t4, 1
    beq t2, t4, print_suffix # if turn is 1 , print 2
    li t3, 39 #  ' in ASCII

print_suffix:

    mv a0, t3 # move suffix to a0
    li a7, 11 # sys. call, print single char
    ecall

print_move_done:
    addi a2, a2, 6 # next frame(frame size is 6 bytes)
    addi a3, a3, 1  # i++

    bgeu a3, s9, print_solution_loop_done
    li a0, 32  # print " " 
    li a7, 11  # sys. call, print single char
    ecall
    j print_solution_loop

print_solution_loop_done:
    j print_solution_done

print_solution_done:

    li a0, 10  # C code '\n'
    li a7, 11 # sys. call, print single char
    ecall

    # Validate results inside the program rather than inspecting output by hand.
    #  s5 : stack root frame, perm and ori are 2 bytes.
    lhu t5, 0(s5) # re: perm = stack[0].perm
    lhu t6, 2(s5) # re: ori = stack[0].ori

    addi a2, s5, 6 # first sol frame: stack[1]
    li a3, 0 # re: index

Re_move_loop:
    bgeu a3, s9, Re_moves_done
    lbu t0, 4(a2) # read this frame's move , 1 byte , offset 4

    # Re: orientation[move][o]

    slli t4, t0, 11 # move * 2048 ( 1024 entries, 2 bytes for uint16_t )
    slli t3, t6, 1 # o*2
    add a1, s2, t4 
    add a1, a1, t3 # get orientation[move][o]
    lhu t6, 0(a1) 

    # Re: permutation[face][p] 
    srli t1, t0, 2 # face,move /4.  0 = R, 1 = B, 2 = D
    andi t2, t0, 3 # turns, 3 in binary is 11. AND to get lower 2 bit, which is turn
    slli t4, t1, 14 # each face has 8192 entries, each 2 bytes. 8192*2 = 2^14
    add t4, s0, t4 # permutation[face] base
    li t1, 0 # turn counter

Re_perm_turn_loop:
    bltu t2, t1, Re_perm_turn_done
    slli t3, t5, 1 # p * sizeof(uint16_t)
    add a1, t4, t3
    lhu t5, 0(a1) # p = permutation[face][p]
    addi t1, t1, 1
    j Re_perm_turn_loop
Re_perm_turn_done:
    addi a2, a2, 6 # next frame
    addi a3, a3, 1 # re index
    j Re_move_loop

Re_moves_done:
    bnez t5, Re_failed
    bnez t6, Re_failed
    li a0, 0
    j Re_exit

Re_failed:
    li a0, 1

Re_exit:
    li a7, 93
    ecall

IDA_moves_done:
    beq s8, s5, IDA_round_done # root frame

    # non root nodes have no moves left, back to upper level
    addi s8, s8, -6
    addi s9, s9, -1
    j IDA_inner_loop

IDA_round_done:
    mv s6, s7   # limit = next_limit
    li t0, 11 # t0 = 11
    bltu t0, s6, IDA_fail  # if limit > 11 , branch
    j IDA_loop_start        

IDA_fail:
    li a0, 1 # end code 1
    li a7, 93 # end program sys. call
    ecall  

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
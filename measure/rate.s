.data
msg: .string "Ripes RV32I smoke test, loop count = "
.text
main:
    la   a0, msg
    li   a7, 4
    ecall
    li   t0, 0
    li   t1, 2000000 # t1 set count N to this number for large scale
    li   t2, 0x10000000 # That's where .data at
    li   t3, 0xAB # t3 for dummy data. (for testing mem write) 
loop:
    sb t3, 0(t2)

    addi t0, t0, 1
    addi t2, t2, 0 # control: address does not move, always write the same byte
    
    bne  t0, t1, loop

    # print total loop count
    mv   a0, t0
    li   a7, 1
    ecall

    # exit
    li   a7, 10
    ecall

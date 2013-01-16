$MOD51				; indicating to ASM51 we are using 8051

; OP_A and OP_B are addresses of MSB in each 32bit operad (big endian)
OP_A EQU 30H		; OP_A is a symbolic constant
OP_B EQU 34H		; OP_B is a symbolic constant

ROT_NUM EQU 2FH	; this is where rotation number will be stored

; input A and B
mov OP_A + 0, #0FEH
mov OP_A + 1, #0DCH
mov OP_A + 2, #0BAH
mov OP_A + 3, #98H

mov OP_B + 0, #76H
mov OP_B + 1, #54H
mov OP_B + 2, #32H
mov OP_B + 3, #10H

; Test vectors for given key
; Plain Text => 0000000000000000 , Cipher Text => EEDBA5216D8F4B15
; Plain Text => A9081726354FB018 , Cipher Text => 72CE518800C2A855
; Plain Text => FEDCBA9876543210 , Cipher Text => EA04BFBEB6EB797B

; place scheduled key in external mem 
; byte 3 is the MSB, byte 0 is the LSB
MOV DPTR, #0000H		; set DPTR to 0

MOV A, #9BH				; key[0] byte 3
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #0BBH			; key[0] byte 2
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #0D8H			; key[0] byte 1
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #0C8H			; key[0] byte 0
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location

MOV A, #1AH				; key[1] byte 3
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #37H				; key[1] byte 2
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #0F7H			; key[1] byte 1
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #0FBH			; key[1] byte 0
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location

MOV A, #46H				; key[2] byte 3
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #0F8H			; key[2] byte 2
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #0E8H			; key[2] byte 1
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #0C5H			; key[2] byte 0
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location

MOV A, #46H				; key[3] byte 3
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #0CH				; key[3] byte 2
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #60H				; key[3] byte 1
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #85H				; key[3] byte 0
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location

MOV A, #70H				; key[4] byte 3
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #0F8H			; key[4] byte 2
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #3BH				; key[4] byte 1
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #8AH				; key[4] byte 0
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location

MOV A, #28H				; key[5] byte 3
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #4BH				; key[5] byte 2
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #83H				; key[5] byte 1
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #03H				; key[5] byte 0
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location

MOV A, #51H				; key[6] byte 3
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #3EH				; key[6] byte 2
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #14H				; key[6] byte 1
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #54H				; key[6] byte 0
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location

MOV A, #0F6H			; key[7] byte 3
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #21H				; key[7] byte 2
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #0EDH			; key[7] byte 1
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #22H				; key[7] byte 0
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location

MOV A, #31H				; key[8] byte 3
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #25H				; key[8] byte 2
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #06H				; key[8] byte 1
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #5DH				; key[8] byte 0
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location

MOV A, #11H				; key[9] byte 3
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #0A8H			; key[9] byte 2
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #3AH				; key[9] byte 1
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #5DH				; key[9] byte 0
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location

MOV A, #0D4H			; key[10] byte 3
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #27H				; key[10] byte 2
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #68H				; key[10] byte 1
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #6BH				; key[10] byte 0
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location

MOV A, #71H				; key[11] byte 3
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #3AH				; key[11] byte 2
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #0D8H			; key[11] byte 1
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #2DH				; key[11] byte 0
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location

MOV A, #4BH				; key[12] byte 3
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #79H				; key[12] byte 2
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #2FH				; key[12] byte 1
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #99H				; key[12] byte 0
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location

MOV A, #27H				; key[13] byte 3
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #99H				; key[13] byte 2
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #0A4H			; key[13] byte 1
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #0DDH			; key[13] byte 0
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location

MOV A, #0A7H			; key[14] byte 3
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #90H				; key[14] byte 2
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #1CH				; key[14] byte 1
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #49H				; key[14] byte 0
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location

MOV A, #0DEH			; key[15] byte 3
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #0DEH			; key[15] byte 2
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #87H				; key[15] byte 1
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #1AH				; key[15] byte 0
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location

MOV A, #36H				; key[16] byte 3
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #0C0H			; key[16] byte 2
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #31H				; key[16] byte 1
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #96H				; key[16] byte 0
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location

MOV A, #0A7H			; key[17] byte 3
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #0EFH			; key[17] byte 2
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #0C2H			; key[17] byte 1
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #49H				; key[17] byte 0
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location

MOV A, #61H				; key[18] byte 3
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #0A7H			; key[18] byte 2
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #8BH				; key[18] byte 1
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #0B8H			; key[18] byte 0
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location

MOV A, #3BH				; key[19] byte 3
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #0AH				; key[19] byte 2
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #1DH				; key[19] byte 1
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #2BH				; key[19] byte 0
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location

MOV A, #4DH				; key[20] byte 3
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #0BFH			; key[20] byte 2
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #0CAH			; key[20] byte 1
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #76H				; key[20] byte 0
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location

MOV A, #0AEH			; key[21] byte 3
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #16H				; key[21] byte 2
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #21H				; key[21] byte 1
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #67H				; key[21] byte 0
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location

MOV A, #30H				; key[22] byte 3
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #0D7H			; key[22] byte 2
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #6BH				; key[22] byte 1
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #0AH				; key[22] byte 0
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location

MOV A, #43H				; key[23] byte 3
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #19H				; key[23] byte 2
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #23H				; key[23] byte 1
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #04H				; key[23] byte 0
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location

MOV A, #0F6H			; key[24] byte 3
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #0CCH			; key[24] byte 2
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #14H				; key[24] byte 1
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #31H				; key[24] byte 0
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location

MOV A, #65H				; key[25] byte 3
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #04H				; key[25] byte 2
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #63H				; key[25] byte 1
MOVX @DPTR, A			; move to external memory
INC DPTR				; point to next location
MOV A, #80H				; key[25] byte 0
MOVX @DPTR, A			; move to external memory

; key placement end
mov DPTR, #0000H		; reset DPTR to 0
;**********************************************************
; we start at byte 0x0003 (S[3]) because its the LSB byte
; and work backwards to add the total 32-bits
; A = A + S[0]
mov R2 , #03			; start at S[3]
mov R0 , #OP_A + 3		; R0 gets the lsb value
acall ADD_EXT

;B = B + S[1];
mov R2 , #07			; S[7] downto S[4] are used
mov R0 , #OP_B + 3		; R0 gets the lsb value
acall ADD_EXT
;**********************************************************

; 12轮加密
; Initialization of loop
mov R6, #01H			; for loop index counter, ascending
mov R7, #0CH			; counter for 12 rounds, descending

;**********************************************************
; RC5的主循环，12轮，每轮的基本操作如下：
; ((A XOR B) <<< B) + S[2*i]   ; 其中i为轮数
; ((B XOR A) <<< A) + S[2*i+1] ; 其中i为轮数

RC5_LOOP:
; (A XOR B)
mov R0, #OP_A			; R0 gets MSB of A
mov R1, #OP_B			; R1 gets MSB of B
acall XOR_EQ
; 执行异或操作后得到的结果存储在R0指向的地址上，即A上

; ((A XOR B) <<< B)
; R2 - R5 存储A的值
mov R2, OP_A + 0		; R2 hold acutal MSB value
mov R3, OP_A + 1
mov R4, OP_A + 2
mov R5, OP_A + 3		; R5 hold acutal LSB value

; R0，R1 存储A的LSB和B的LSB的间接地址
mov R0, #OP_A + 3 		; R0 points to LSB value
mov R1, #OP_B + 3		; R1 holds the rotate-by value
acall LR32

; ((A XOR B) <<< B) + S[2 * i]
mov R0, #OP_A + 3		; R0 gets the LSB of A
mov A, R6				; store the current index to A
mov B, #02H				; constant
mul AB					; 2 * i
mov B, #04H				; move to i-round keys
mul AB
add A, #03H				; move to the MSB byte
mov R2, A				; R2 points to the LSB byte of S[i]
acall ADD_EXT 

;**********************************************************
; exactly the same as above, A and B are reversed
;  (B XOR A)
mov R0, #OP_B 
mov R1, #OP_A 
acall XOR_EQ

;  (B XOR A) <<< A
mov R2, OP_B + 0
mov R3, OP_B + 1
mov R4, OP_B + 2
mov R5, OP_B + 3
mov R0, #OP_B + 3
mov R1, #OP_A + 3
lcall LR32

;  ((B XOR A) <<< A) + S[2 * i + 1];
mov R0, #OP_B + 3
mov A, R6
mov B, #02H 
mul AB
inc A         ; 就比上面的操作多了这一条
mov B, #04H
mul AB
add A, #03H
mov R2, A
lcall ADD_EXT 

inc R6					; increment index
djnz R7, RC5_LOOP		; decrement counter

nop						; place breakpoint here
; 把生成的结果输出到P0 - P3输出端口
mov P0, 30H
mov P1, 31H
mov P2, 32H
mov P3, 33H
I_LOOP:
sjmp I_LOOP
ret ; end of all codes

;**********************************************************
; 完成32bit（4byte）的加法操作
; parameter to pass in: R0, R2
; R0 will byte we're add the s[i] with
; R2 will point to the states s[0] -> s[i]
; Since DPTR max value is 0x0067, we can safely ignore DPH
ADD_EXT:
mov dpl , R2 			; set DPTR to LSB of byte to add
mov R1, #04H  			; set counter to 4
clr c 					; clear the carry.
ADD_EXT_LOOP:
movx A, @dptr 			; get byte from external mem
addc A, @R0 			; add byte from the target
mov @R0, A 				; save in the target
dec R0 					; goto next byte
dec dpl 				; goto next byte
djnz R1, ADD_EXT_LOOP 	; loop
clr c 					; clear the carry.
ret

;**********************************************************
; 执行32bit（4byte）的异或操作
; parameter to pass in: R0, R1
; R0 will point to the target
; R1 will point to the source
XOR_EQ:
mov R2, #04H			; set counter to 4
XOR_EQ_LOOP:
mov A, @R0 				; get byte from the source
xrl A, @R1 				; R0 <- R0 xor R1
mov @R0, A 				; save in the target
inc R0
inc R1
djnz R2, XOR_EQ_LOOP	; 32-bit value, loop 4 times
ret

;**********************************************************
; LR32就是完成了数据顺序循环的操作
; 这里采用的是把要循环的数字分解成16，8，1（因为最多循环31，由R1模32得到）
; parameter to pass in: R0, R1, R2, R3, R4, R5
; R0 is a point to the LSB byte of the source
; R1 holds the rotate-by value
; R2 contains the actual MSB byte
; then R3 gets next byte and so does R4
; R5 contains the actual LSB byte
LR32:
clr C;
mov A, @R1 				; load rotate-by value
anl A, #1FH 			; reduce to 5 bits
mov R1, A 				; stored last 5-bits back
jz END_CODE 			; no rotate required, jump to end

; 16-bit rotate simply swaps the low and high 16-bits
; for example 0xff1a6185, rotate by 16-bits produces 0x6185ff1a
mov A, R1 				; A has the rotate-by value
jnb ACC.4, ROTATE8 		; skip rotate 16-bit, jump to rotate 8-bit
mov A, R4
xch A, R2 				; swap R4 and R2
mov R4, A 				; stored swap value back
mov A, R5 
xch A, R3 				; swap R5 and R3
mov R5, A 				; stored swap value back

ROTATE8:
; 8-bit rotate moves the msb value to the lsb location
; in 0xff1a6185, rotate by 8-bit produces 0x1a6185ff
; the XCH instr swaps the Accum value with the reg. value
; we call the XCH instr 3 times since its a 32-bit value
mov A, R1 				; restore rotate-by value
jnb ACC.3, ROTATE3 		; skip rotate 8-bit, jump to rotate 3-bit
mov A, R2 				
xch A, R3 				
mov R2, A 				
mov A, R3
xch A, R4
mov R3, A
mov A, R4
xch A, R5
mov R4, A

ROTATE3:
mov A, R1 				; restore rotate-by value
anl A, #07H				; reduce to 3bits
jz END_CODE 			; no rotate required, jump to end
mov R1, A 				; save the last 3 bits

LOOP:
mov A, R2 				; mov msb value to A
mov C, ACC.7 			; get the msb bit, store the LSB bit of A (or B) in the carry flag
mov A, R5
rlc A 					; rotate R5 by 1-bit
mov R5, A
mov A, R4
rlc A 					; rotate R4 by 1-bit
mov R4, A
mov A, R3
rlc A 					; rotate R3 by 1-bit
mov R3, A
mov A, R2
rlc A 					; rotate R2 by 1-bit
mov R2, A
djnz R1, LOOP 			; max loop is 7 times

END_CODE:
; 移位后的结果存回A（或B）的原始地址
mov A, R5
mov @R0, A 				; move R5 value to mem loc. 0x33
dec R0
mov A, R4
mov @R0, A 				; move R4 value to mem loc. 0x32
dec R0
mov A, R3
mov @R0, A 				; move R3 value to mem loc. 0x31
dec R0
mov A, R2
mov @R0, A 				; move R2 value to mem loc. 0x30
dec R0
ret

end
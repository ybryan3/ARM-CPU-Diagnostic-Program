	AREA	|.text|, CODE, READONLY, ALIGN=2
	THUMB
	EXPORT Start
Start		

MAIN	
		SUB R0, R0, R0 		; R0 = 0 1110 000 0010 0 1111 0000 0000 0000 1111 E04F000F
		ADD R2, R0, #5 		; R2 = 5 1110 001 0100 0 0000 0010 0000 0000 0101 E2802005
		ADD R3, R0, #12		 ; R3 = 12 1110 001 0100 0 0000 0011 0000 0000 1100 E280300C
		SUB R7, R3, #9 		; R7 = 3 1110 001 0010 0 0011 0111 0000 0000 1001 E2437009
		ORR R4, R7, R2 		; R4 = 3 OR 5 = 7 1110 000 1100 0 0111 0100 0000 0000 0010 E1874002
		AND R5, R3, R4 		; R5 = 12 AND 7 = 4 1110 000 0000 0 0011 0101 0000 0000 0100 E0035004
		ADD R5, R5, R4 		; R5 = 4 + 7 = 11 1110 000 0100 0 0101 0101 0000 0000 0100 E0855004
		SUBS R8, R5, R7		 ; R8 = 11 - 3 = 8, set Flags 1110 000 0010 1 0101 1000 0000 0000 0111 E0558007
		BEQ END 			; shouldn't be taken 0000 1010 0000 0000 0000 0000 0000 1100 0A00000C
		SUBS R8, R3, R4		 ; R8 = 12 - 7 = 5 1110 000 0010 1 0011 1000 0000 0000 0100 E0538004
		BGE AROUND 			; should be taken 1010 1010 0000 0000 0000 0000 0000 0000 AA000000
		ADD R5, R0, #0 		; should be ski pped 1110 001 0100 0 0000 0101 0000 0000 0000 E2805000
AROUND 	SUBS R8, R7, R2 	; R8 = 3 - 5 = -2, set Flags 1110 000 0010 1 0111 1000 0000 0000 0010 E0578002
		ADDLT R7, R5, #1	 ; R7 = 11 + 1 = 12 1011 001 0100 0 0101 0111 0000 0000 0001 B2857001
		SUB R7, R7, R2 		; R7 = 12 - 5 = 7 1110 000 0010 0 0111 0111 0000 0000 0010 E0477002
		;STR R7, [R3, #84]	 ; mem[12+84] = 7 1110 010 1100 0 0011 0111 0000 0101 0100 E5837054
		;LDR R2, [R0, #96]	 ; R2 = mem[96] = 7 1110 010 1100 1 0000 0010 0000 0110 0000 E5902060
		
		LDR R1, =0xE000E000
		ADD R1, R1, #84
		STR R7, [R3, R1]	; mem [0xE000E060]
		LDR R1, =0xE000E000
		ADD R1, R1, #96
		LDR R2, [R0, R1] 	; R2 = mem[96] = 7
		
		LDR R1, =0xE000E000
		ADD R1, R1, #100
		
		ADD R15, R15, R0	 ; PC = PC+8 (skips next) 1110 000 0100 0 1111 1111 0000 0000 0000 E08FF000
		ADD R2, R0, #14		 ; shouldn't happen 1110 001 0100 0 0000 0010 0000 0000 0001 E280200E
		B END 				; always taken 1110 1010 0000 0000 0000 0000 0000 0001 EA000001
		ADD R2, R0, #13		 ; shouldn't happen 1110 001 0100 0 0000 0010 0000 0000 0001 E280200D
		ADD R2, R0, #10 		; shouldn't happen 1110 001 0100 0 0000 0010 0000 0000 0001 E280200A
END 	STR R2, [R0, R1] 		; mem[100] = 7 1110 010 1100 0 0000 0010 0000 0101 0100 E5802064
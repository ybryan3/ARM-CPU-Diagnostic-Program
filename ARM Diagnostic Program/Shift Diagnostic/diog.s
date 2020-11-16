	AREA	|.text|, CODE, READONLY, ALIGN=2
	THUMB
	EXPORT Start
Start		

		MOV R0, #0X00000001
		LSL R1, R0, #1
		LSL R2, R1, R1
		LSR R3, R2, #1
		LSR R4, R2, R1
		ASR R3, R3, #1
		ASR R3, R3, R1
		ROR R2, R2, R1
		ROR R3, R2, #1
		MOV R0, #0
		MOV R0, #0
		
END
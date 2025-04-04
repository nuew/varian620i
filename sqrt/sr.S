*
* This is in the public domain in the United States, as it is a work
* of the U.S. Government made by an employee in the course of their
* official duties per 17 USC 105.
*
* SUBROUTINE SR COMPUTES THE SQUARE ROOT OF THE INPUT A REGISTER.
* CERTAIN STRINGENT LIMITS ARE PLACED ON THE INPUT. IT MUST ALWAYS BE
* A WHOLE INTEGER, ALWAYS POSITIVE, ALWAYS GREATER THAN ZERO BUT LESS
* THAN 32,767 AND ALWAYS SCALED 2**15 (OFB). THE NEAREST WHOLE SQUARE
* ROOT IS RETURNED IN THE A REGISTER AND THE X AND B REGISTERS ARE RE-
* STORED TO THEIR INPUT VALUES. FOR EXAMPLE, AN INPUT OF 30 (BASE 10)
* WILL YIELD A SQUARE ROOT OF 5, WHEREAS AN INPUT OF 31 WILL YIELD A
* SQUARE ROOT OF 6
*
        ORG     02634       GUARANTEED LOCATION FOR USE BY AV
SR      ENTR
        STB     SR4+3       SAVE REGISTERS
        STA     SR4+4
        STA     SR4         A
        STA     SR4+1       1ST XI
        STA     SR4+2       1ST XI
        ASRA    1           NUMBER OF PASSES
        TAX
SR1     TZA
        LDB     SR4         A
        DIV     SR4+1       A/XI
        TBA
        ADD     SR4+1       XI + A/XI
        ASRA    1           1/2*(XI + A/XI)= NEW XI
        STA     SR4+1       NEW XI
        SUB     SR4+2       MINUS OLD XI
        JAP     *+9         IF NEW XI GREQ OLD XI QUIT
        LDA     SR4+1       NEW XI
        STA     SR4+2       TO OLD XI FOR NEW PASS
        JXZ     *+5         IF NUMBER OF PASSES EQ 1/2 A, QUIT
        DXR
        JMP     SR1         DO NEXT PASS
        LDB     SR4+1
        TZA
        MUL     SR4+1       XI**2
        STB     SR4+2
        LDA     SR4         A
        SUB     SR4+2       A-(XI**2)
        JAZ     *+9         IF XI**2 IS EQUAL OR LARGER, OK
        JAN     *+7
        STA     SR4+2       IF NOT, SAVE DIFFERENCE
        LDA     SR4+1       CHECK AGAINST XI
        SUB     SR4+2
        JAN     SR4-3       XI IS LARGER SO ROUND UP XI
        LDA     SR4+1       XI IS SMALLER OR EQUAL SO OK
        LDB     SR4+3       RESTORE REGISTERS
        LDX     SR4+4
        JMP     SR          EQRESS
        INR     SR4+1       ROUND UP XI
        JMP     *-6         RESTORE REGISTERS
SR4     CATA    0,0,0,0,0

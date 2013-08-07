IFNDEF VESEH_INC
VESEH_INC EQU <1>

ExceptionContinueExecution      EQU 0
ExceptionContinueSearch         EQU 1
ExceptionNestedException        EQU 2
ExceptionCollidedUnwind         EQU 3

; Значения, используемые в фильтрах
EXCEPTION_EXECUTE_HANDLER       EQU 1
EXCEPTION_CONTINUE_SEARCH       EQU 0
EXCEPTION_CONTINUE_EXECUTION    EQU (-1)

EXCEPTION_NONCONTINUABLE        EQU 00000001h
EXCEPTION_UNWINDING             EQU 00000002h
EXCEPTION_EXIT_UNWIND           EQU 00000004h
EXCEPTION_STACK_INVALID         EQU 00000008h
EXCEPTION_NESTED_CALL           EQU 00000010h
EXCEPTION_TARGET_UNWIND         EQU 00000020h
EXCEPTION_COLLIDED_UNWIND       EQU 00000040h

; EXCEPTION_REGISTRATION - структура регистрации обработчиков исключений
EXCEPTION_REGISTRATION STRUCT
    Next DWORD ?
    Handler DWORD ?
EXCEPTION_REGISTRATION ENDS
PEXCEPTION_REGISTRATION EQU PTR EXCEPTION_REGISTRATION

; EXCEPTION_POINTERS
EXCEPTION_POINTERS STRUCT
    ExceptionRecord DWORD ?
    ContextRecord DWORD ?
EXCEPTION_POINTERS ENDS
PEXCEPTION_POINTERS EQU PTR EXCEPTION_POINTERS

; EXCEPTION_RECORD
EXCEPTION_MAXIMUM_PARAMETERS EQU 15
EXCEPTION_RECORD STRUCT
    ExceptionCode DWORD ?
    ExceptionFlags DWORD ?
    ExceptionRecord LPVOID ?
    ExceptionAddress DWORD ?
    NumberParameters DWORD ?
    ExceptionInformation DWORD EXCEPTION_MAXIMUM_PARAMETERS dup (?)
EXCEPTION_RECORD ENDS
PEXCEPTION_RECORD EQU PTR EXCEPTION_RECORD

; SCOPETABLE_ENTRY
SCOPETABLE_ENTRY STRUCT
    EnclosingLevel DWORD ?
    FilterProc DWORD ?
    HandlerProc DWORD ?
SCOPETABLE_ENTRY ENDS

; SEH - Structured Exception Handling
SEH_FRAME STRUCT
    StackPointerValue DWORD ?
    ExceptionPointers DWORD ?
    RegFrame EXCEPTION_REGISTRATION <?>
    ScopeTable DWORD ?
    TryLevel DWORD ?
    StackFrameBase DWORD ?
SEH_FRAME ENDS
PSEH_FRAME EQU PTR SEH_FRAME

; CONTEXT - Whole processor's state
SIZE_OF_80387_REGISTERS EQU 80
MAXIMUM_SUPPORTED_EXTENSION EQU 512

FLOATING_SAVE_AREA STRUCT
        ControlWord             DWORD ?
        StatusWord              DWORD ?
        TagWord                 DWORD ?
        ErrorOffset             DWORD ?
        ErrorSelector           DWORD ?
        DataOffset              DWORD ?
        DataSelector            DWORD ?
        RegisterArea            BYTE SIZE_OF_80387_REGISTERS dup (?)
        Cr0NpxState             DWORD ?
FLOATING_SAVE_AREA ENDS

CONTEXT STRUCT
        ContextFlags            DWORD ?

        iDr0                    DWORD ?
        iDr1                    DWORD ?
        iDr2                    DWORD ?
        iDr3                    DWORD ?
        iDr6                    DWORD ?
        iDr7                    DWORD ?

        FloatSave               FLOATING_SAVE_AREA <>

        regGs                   DWORD ?
        regFs                   DWORD ?
        regEs                   DWORD ?
        regDs                   DWORD ?

        regEdi                  DWORD ?
        regEsi                  DWORD ?
        regEbx                  DWORD ?
        regEdx                  DWORD ?
        regEcx                  DWORD ?
        regEax                  DWORD ?
        regEbp                  DWORD ?
        regEip                  DWORD ?

        regCs                   DWORD ?
        regFlag                 DWORD ?
        regEsp                  DWORD ?
        regSs                   DWORD ?
        ExtendedRegisters       BYTE MAXIMUM_SUPPORTED_EXTENSION dup(?)
CONTEXT ENDS
PCONTEXT EQU PTR CONTEXT
;
;

ENDIF

; ###################################################################################
;
;   ��������:
;     ���������� ��������� ����������� ��������� ���������� ��� �����������
;     MSVC � �������������� SEH. ������ ���������� ��������� ������������
;     ����� __try // __finally � __try // __except � ����������, ����������
;     �� C � C++ ��� ������������� run-time ���������� MSVCRT.
;
;   ����������:
;     ml.exe /c /coff /nologo /Cp /Gz veseh.asm
;     link.exe /nologo /noentry /dll /def:%DEFS% /opt:ref /libpath:<libs>
;
;   ������:
;     v1.06 (c) milabs/github, 2013
;
; ###################################################################################

        .686
        .model flat

        include include\win32.inc
        include include\veseh.inc

        include ntdll.inc
        includelib ntdll.lib


; ###################################################################################

        .code

ENABLE_VECTORED_SEH EQU 1

; ###################################################################################
; SEH_prolog
;
;   ��������:
;       ������ ��� �������, ������������ SEH. ��������� ����������� ���
;       ��������� SEH ����� �����. ������������� ���������� ����������
;       __except_handler3. ������������ ������������ ��������� �������:
;
;       SomeFunctionThatWantsSEH:
;           push        SizeOfLocalVariables + 8
;           push        OFFSET ScopeTable
;           call        __SEH_prolog
;            ...
;
;       ���� �� ���������� (ESP-based):
;           ��������    ��������
;           --------    --------
;   ESP =>   00         ����� ��������
;           +04         OFFSET ScopeTable
;           +08         SizeOfLocalVariables + 8
;
;       ���� ����� ���������� (EBP-based):
;           ��������    ��������
;           --------    --------
;   ESP =>  -(S + 40)   ����� �������� �� __SEH_prolog
;           -(S + 36)   EDI
;           -(S + 32)   ESI
;           -(S + 28)   EBX
;           -(S + 24)   ��������� ���������� ������� SomeFunctionThatWantsSEH
;                       (���� ��������� ����������, S = SizeOfLocalVariables)
;                       struct SEH_FRAMEx {
;           -24             DWORD StackPointerValue;
;           -20             PEXCEPTION_POINTERS ExceptionPointers;
;                           struct EXCEPTION_REGISTRATION RegFrame {
;           -16                 struct EXCEPTION_REGISTRATION * Next;
;           -12                 LPVOID Handler;
;                           };
;           -08             DWORD ScopeTable;
;           -04             DWORD TryLevel;
;   EBP =>   00             DWORD StackFrameBase;
;                       };
;           +04         ����� �������� �� ������� SomeFunctionThatWantsSEH
;           +08         ��������� �������
;             --------  --------
; ###################################################################################
        ALIGN 16

_SEH_prolog PROC C
        ASSUME  fs:nothing

        push    OFFSET _except_handler3
        mov     eax, DWORD PTR fs:[0]
        push    eax
        mov     eax, [esp + 16]
        mov     [esp + 16], ebp
        lea     ebp, [esp + 16]
        sub     esp, eax
        push    ebx
        push    esi
        push    edi
        mov     eax, [ebp - 8]
        mov     [ebp - 24], esp
        push    eax
        mov     eax, [ebp - 4]
        mov     DWORD PTR [ebp - 4], -1
        mov     [ebp - 8], eax
        lea     eax, [ebp - 16]
        mov     fs:[0], eax

        ret
_SEH_prolog ENDP

; ###################################################################################
; SEH_epilog
;
;   ��������:
;       ������ ��� �������, ������������ SEH. ������ ����, ������� �������������
;       ���������� ����������  ������������ ������������ ��������� �������:
;
;       SomeFunctionThatWantsSEH:
;           ...
;           mov         eax, [FunctionResult]
;           call        __SEH_epilog
;           ret
; ###################################################################################
        ALIGN 16

_SEH_epilog PROC C
        ASSUME  fs:nothing

        mov     ecx, [ebp - 16]
        mov     fs:[0], ecx
        pop     ecx
        pop     edi
        pop     esi
        pop     ebx
        mov     esp, ebp
        pop     ebp
        push    ecx

        ret
_SEH_epilog ENDP

; ###################################################################################
; ExceptionHandler
;
;   ��������: 
;       ������� ������� ��������� ����������. �������������� ��� _except_handler3.
;       � �������� ������ ������� ������ ��������� ������������, ��������� � ������
;       ������� �������� ScopeTable. ���� ��������� ������� ������� �������� �������-
;       ������, �� � ����� ����������, ����� �� ������ ����������. � ���� ������,
;       �������������� ��� �����, � ���������� ������� �� ������������. ����� �������
;       ����������� ���������� ���������� � ��������� ���������.
;
; ###################################################################################
        ALIGN 16

_except_handler3 PROC C uses esi edi ebx, \
                pException:PEXCEPTION_RECORD, \
                pEstablisher:LPVOID, \
                pContext:PCONTEXT,\
                pDispatcher:LPVOID
; local variables
        LOCAL   ExceptionPointers:EXCEPTION_POINTERS

; function's code
        cld
        xor     edi, edi

        mov     ecx, pException
        mov     ebx, pEstablisher
        
        ; �������� ������ ������.
        test    [ecx][EXCEPTION_RECORD.ExceptionFlags], (EXCEPTION_UNWINDING OR EXCEPTION_EXIT_UNWIND)
        jnz     @@unwinding

        ; ��������� ExceptionPointers
        mov     eax, pContext
        lea     esi, ExceptionPointers
        mov     [ebx][-8][SEH_FRAME.ExceptionPointers], esi
        mov     [esi][EXCEPTION_POINTERS.ContextRecord], eax
        mov     [esi][EXCEPTION_POINTERS.ExceptionRecord], ecx

        mov     esi, [ebx][-8][SEH_FRAME.TryLevel]
        mov     edi, [ebx][-8][SEH_FRAME.ScopeTable]
@@for_each_item:
        cmp     esi, -1
        je      @@ExceptionContinueSearch
        ; ��������� ��� �����: try-except ��� try-finally?
        lea     eax, [esi + esi * 2]
        mov     eax, [edi + eax * 4][SCOPETABLE_ENTRY.FilterProc]
        or      eax, eax
        jz      @@iterate
        ; ��������� ���������-������ � ������� ���������
        call    RunWithStackChange
        
        or      eax, eax
        jz      @@iterate
        js      @@ExceptionContinueExecution

        ; ������ ������ �� ���������� ����������� ����������. �������,
        ; ��� ������ ��������� ���������� ���������...
        push    ebx
        call    _global_unwind2
	add	esp, 4
        ; .. �����, ���������...
        push    esi
        push    ebx
        call    _local_unwind2
	add	esp, 8
        ; .. � �����, �������� ������� ������� ����������� � ��������� ����������.
        lea     edx, [esi + esi * 2]
        mov     eax, [edi + edx * 4][SCOPETABLE_ENTRY.HandlerProc]
        mov     edx, [edi + edx * 4][SCOPETABLE_ENTRY.EnclosingLevel]
        mov     [ebx][-8][SEH_FRAME.TryLevel], edx
        call    RunWithStackChange
        ; ���� �� �� ������������!

    @@iterate:
        lea     eax, [esi + esi * 2]
        mov     esi, [edi + eax * 4][SCOPETABLE_ENTRY.EnclosingLevel]
        jmp     @@for_each_item

@@ExceptionContinueSearch:
        mov     eax, ExceptionContinueSearch
        jmp     @@return

@@ExceptionContinueExecution:
        mov     eax, ExceptionContinueExecution
        jmp     @@return

@@unwinding:
        push    -1
        push    ebx
        call    _local_unwind2
	add	esp, 8
        mov     eax, ExceptionContinueSearch

@@return:
        ret
_except_handler3 ENDP

; ###################################################################################
; RunWithStackChange
;
;   ��������:
;       ��������� ���������, �� ������ ��������� ���������, � ������������ �
;       ��������� �������.
;
;   ��������� [FASTCALL]:
;       EAX - ����� ��������� ��� ����������.
;       EBX - ��������� �� ����� EXCEPTION_REGISTRATION.
;
; ###################################################################################
        ALIGN 16

RunWithStackChange PROC uses esi edi ebx ebp
        lea     ebp, [ebx][-8][SEH_FRAME.StackFrameBase]
        xor     ebx, ebx
        xor     ecx, ecx
        xor     edx, edx
        xor     edi, edi
        xor     esi, esi
        call    eax
        ret
RunWithStackChange ENDP

; ###################################################################################
; GlobalUnwind
;
;   ��������: 
;       ������� ������������ ���������� ��������� ������������ ����������. ���������
;       �������������� �� ������, ���������� ��� exFrame.
;
; ###################################################################################
        ALIGN 16

IFDEF ENABLE_VECTORED_SEH
_global_unwind2 PROC C uses esi edi ebx, \
                pEstablisher:PEXCEPTION_REGISTRATION
; local variables
        LOCAL   TheContext:CONTEXT
        LOCAL   TheException:EXCEPTION_RECORD

; function's code
        lea     edi, TheContext
        call    @@init_context
        lea     esi, TheException
        call    @@init_exception

        mov     ebx, fs:[0]
@@for_each_frame:
        ; ���������, ��������� �� ����� ������?
        cmp     ebx, -1
        je      @@return
        ; ���������, ��������� �� ������ �����?
        cmp     ebx, pEstablisher
        je      @@return

        ; �������� ���������� ���������������� ������ �����������.
        xor     eax, eax
        mov     edx, OFFSET @@NestedHandler
        call    SafeExecuteHandler
        ; ��������� ������������ ������������� ��������.
        cmp     eax, 3
        jg      @@status_C0000026
        ; ��������� ����������
        and     eax, 3
        lea     eax, [OFFSET @@jump_table + eax * 4]
        jmp     DWORD PTR [eax]

    @@unlink:
        mov     ebx, [ebx][EXCEPTION_REGISTRATION.Next]
        mov     fs:[0], ebx
        jmp     @@for_each_frame

@@return:
        ret

@@status_C0000026:
        mov     eax, STATUS_INVALID_DISPOSITION
        call    MyRaiseException

@@jump_table:
        dd OFFSET @@status_C0000026     ; ExceptionContinueExecution
        dd OFFSET @@unlink              ; ExceptionContinueSearch
        dd OFFSET @@status_C0000026     ; ExceptionNestedException
        dd OFFSET @@unlink              ; ExceptionCollidedUnwind

@@init_context:
        cld
        mov     ecx, SIZEOF(CONTEXT)
        xor     eax, eax
        rep     stosb
        retn
@@init_exception:
        mov     edx, [ebp + 4]
        mov     [esi][EXCEPTION_RECORD.ExceptionCode], STATUS_UNWIND
        mov     [esi][EXCEPTION_RECORD.ExceptionFlags], EXCEPTION_UNWINDING
        mov     [esi][EXCEPTION_RECORD.ExceptionRecord], edi
        mov     [esi][EXCEPTION_RECORD.NumberParameters], edi
        mov     [esi][EXCEPTION_RECORD.ExceptionAddress], edx
        cmp     pEstablisher, 0
        jz      @@ihret
        or      [esi][EXCEPTION_RECORD.ExceptionFlags], EXCEPTION_EXIT_UNWIND
    @@ihret:
        retn
@@NestedHandler:
        mov     eax, ExceptionContinueSearch
        retn
_global_unwind2 ENDP

; ###################################################################################
; SafeExecuteHandler
;
;   ��������: 
;       ������������ ���������� ����� ������� �� ������ �����.
;
;   ���������:
;       EAX = pDispatcherFrame
;       EDX = pfnSafeHandler
;       EBX = pEstablisher
;       EDI = pContext
;       ESI = pException
;
; ###################################################################################
        ALIGN 16

SafeExecuteHandler PROC uses esi edi ebx
        ; ��������� ����������
        push    edx
        push    fs:[0]
        mov     fs:[0], esp
        ; �������������� �������� ��� ������
        mov     ecx, [ebx][EXCEPTION_REGISTRATION.Handler]
        push    eax
        push    edi
        push    ebx
        push    esi
        call    ecx
        ; ����� ��� ��������� ���, ��� ����, ����� �� �������� �� ���������� ������ -
        ; ���� �� __cdecl ��� __stdcall, ������ ������ �� ����������.
        mov     esp, fs:[0]
        pop     fs:[0]
        add     esp, 4
        ret
SafeExecuteHandler ENDP

;
; EAX = ExeptionCode, ESI = ExceptionRecord
;
MyRaiseException PROC
; local variables
        LOCAL Exception:EXCEPTION_RECORD

; function's code
        lea     edi, Exception
        mov     [edi][EXCEPTION_RECORD.ExceptionCode], eax
        mov     [edi][EXCEPTION_RECORD.ExceptionFlags], EXCEPTION_NONCONTINUABLE
        mov     [edi][EXCEPTION_RECORD.ExceptionRecord], esi
        mov     [edi][EXCEPTION_RECORD.NumberParameters], 0
        call    RtlRaiseException
MyRaiseException ENDP

ELSE
_global_unwind2 PROC C uses esi edi ebx, \
                pEstablisher:PEXCEPTION_REGISTRATION
; function's code
        push    0
        push    0
        push    OFFSET @@return
        push    pEstablisher
        call    RtlUnwind
@@return:
        ret
_global_unwind2 ENDP
ENDIF

; ###################################################################################
; LocalUnwind
;
;   ��������:
;       ������� ������������ ��������� ��������� ������������, ��������� � �������
;       pEstablisher ����� ������� ScopeTable. ��������� �������������� �� ������
;       ����������� nTryLevel.
;
; ###################################################################################
        ALIGN 16

_local_unwind2 PROC C uses esi edi ebx, \
                pEstablisher:PEXCEPTION_REGISTRATION, \
                nTryLevel:DWORD
; function's code
        ASSUME  fs:nothing

        push    OFFSET @@NestedHandler
        push    fs:[0]
        mov     fs:[0], esp

        mov     ebx, pEstablisher
        mov     esi, [ebx][-8][SEH_FRAME.TryLevel]
        mov     edi, [ebx][-8][SEH_FRAME.ScopeTable]
@@for_each_item:
        ; ��������� ����� �������?..
        cmp     esi, -1
        je      @@done
        ; ��������� ��������� ������� ���������?..
        cmp     esi, nTryLevel
        je      @@done
        ; �������� ������� ������� ������
        lea     edx, [esi + esi * 2]
        mov     esi, [edi + edx * 4][SCOPETABLE_ENTRY.EnclosingLevel]
        mov     [ebx][-8][SEH_FRAME.TryLevel], esi
        ; ����������, ��������� �� ����� �����������
        mov     ecx, [edi + edx * 4][SCOPETABLE_ENTRY.FilterProc]
        mov     eax, [edi + edx * 4][SCOPETABLE_ENTRY.HandlerProc]
        test    ecx, ecx
        jnz     @@for_each_item
        ; ����� �����������
        call    RunWithStackChange
        jmp     @@for_each_item

@@done:
        pop     fs:[0]
        add     esp, 4
        ret

@@NestedHandler:
        mov     eax, ExceptionContinueSearch
        retn
_local_unwind2 ENDP

IFDEF ENABLE_VECTORED_SEH
; ###################################################################################
; VeSehDispatchException
;
;   ��������:
;       ������� ������������ ���������� ��������������� ������������ ����������.
;
; ###################################################################################
        ALIGN 16

VeSehDispatchException PROC uses esi edi ebx, \
                pExceptionInfo:PEXCEPTION_POINTERS
; function's code
        mov     eax, pExceptionInfo
        mov     edi, [eax][EXCEPTION_POINTERS.ContextRecord]
        mov     esi, [eax][EXCEPTION_POINTERS.ExceptionRecord]

        mov     ebx, fs:[0]
@@for_each_frame:
        ; ���� � �������� ������ �� ���������� �� ������ �����������,
        ; ������������ ���������� STATUS_NONCONTINUABLE_EXCEPTION.
        cmp     ebx, -1
        je      @@status_C0000025

        ; �������� ���������� ����������� �������� ������.
        xor     eax, eax
        mov     edx, OFFSET @@NestedHandler
        call    SafeExecuteHandler

        ; �������� ������������ ������������� ��������.
        cmp     eax, 3
        jg      @@status_C0000026
        ; ���� � ���������� ��� ���������� ���� ���� �� ������,
        ; ������������ ���������� STATUS_NONCONTINUABLE_EXCEPTION.
        test    [esi][EXCEPTION_RECORD.ExceptionFlags], (EXCEPTION_NONCONTINUABLE OR EXCEPTION_STACK_INVALID)
        jnz     @@status_C0000025
        ; ��������� ����������
        and     eax, 3
        lea     eax, [OFFSET @@jump_table + eax * 4]
        jmp     DWORD PTR [eax]

    @@iterate:
        mov     ebx, [ebx][EXCEPTION_REGISTRATION.Next]
        jmp     @@for_each_frame

@@return:
        ; � ������������ � ������� ������ VEH, ����� �������� ������� ���������
        ; ����������, �� ������ ������ ���������� ������ (1).
        mov     eax, 1
        ret

@@jump_table:
        dd OFFSET @@return              ; ExceptionContinueExecution
        dd OFFSET @@iterate             ; ExceptionContinueSearch
        dd OFFSET @@iterate             ; ExceptionNestedException
        dd OFFSET @@status_C0000026     ; ExceptionCollidedUnwind

@@status_C0000025:
        mov     eax, STATUS_NONCONTINUABLE_EXCEPTION
        call    MyRaiseException
@@status_C0000026:
        mov     eax, STATUS_INVALID_DISPOSITION
        call    MyRaiseException

@@NestedHandler:
        mov     eax, ExceptionContinueSearch
        retn
VeSehDispatchException ENDP

ENDIF

        END

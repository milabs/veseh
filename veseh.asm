; ###################################################################################
;
;   ОПИСАНИЕ:
;     Реализация поддержки расширенной обработки исключений для компилятора
;     MSVC с использованием SEH. Данная библиотека позволяет использовать
;     блоки __try // __finally и __try // __except в программах, написанных
;     на C и C++ без использования run-time библиотеки MSVCRT.
;
;   КОМПИЛЯЦИЯ:
;     ml.exe /c /coff /nologo /Cp /Gz veseh.asm
;     link.exe /nologo /noentry /dll /def:%DEFS% /opt:ref /libpath:<libs>
;
;   ВЕРСИЯ:
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
;   ОПИСАНИЕ:
;       Пролог для функции, используещей SEH. Формирует необходимый для
;       обработки SEH фрейм стека. Устанавливает обработчик исключений
;       __except_handler3. Используется компилятором следующим образом:
;
;       SomeFunctionThatWantsSEH:
;           push        SizeOfLocalVariables + 8
;           push        OFFSET ScopeTable
;           call        __SEH_prolog
;            ...
;
;       Стек до выполнения (ESP-based):
;           Смещение    Описание
;           --------    --------
;   ESP =>   00         Адрес возврата
;           +04         OFFSET ScopeTable
;           +08         SizeOfLocalVariables + 8
;
;       Стек после выполнения (EBP-based):
;           Смещение    Описание
;           --------    --------
;   ESP =>  -(S + 40)   Адрес возврата из __SEH_prolog
;           -(S + 36)   EDI
;           -(S + 32)   ESI
;           -(S + 28)   EBX
;           -(S + 24)   Локальные переменные функции SomeFunctionThatWantsSEH
;                       (окно локальных переменных, S = SizeOfLocalVariables)
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
;           +04         Адрес возврата из функции SomeFunctionThatWantsSEH
;           +08         Аргументы функции
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
;   ОПИСАНИЕ:
;       Эпилог для функции, используещей SEH. Чистит стек, снимает установленный
;       обработчик исключений  Используется компилятором следующим образом:
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
;   ОПИСАНИЕ: 
;       Главная функция обработки исключений. Экспортируется как _except_handler3.
;       В процессе работы обходит список локальных обработчиков, связанных с данным
;       фреймом таблицей ScopeTable. Если очередной элемент таблицы содержит функцию-
;       фильтр, то её вызов определяет, будет ли вызван обработчик. В этом случае,
;       осуществляется его вызов, а управление обратно не возвращается. Перед вызовом
;       обработчика происходит глобальная и локальная раскрутка.
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
        
        ; Проверка режима работы.
        test    [ecx][EXCEPTION_RECORD.ExceptionFlags], (EXCEPTION_UNWINDING OR EXCEPTION_EXIT_UNWIND)
        jnz     @@unwinding

        ; Настройка ExceptionPointers
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
        ; Проверяем тип блока: try-except или try-finally?
        lea     eax, [esi + esi * 2]
        mov     eax, [edi + eax * 4][SCOPETABLE_ENTRY.FilterProc]
        or      eax, eax
        jz      @@iterate
        ; Выполнить выражение-фильтр и оценить результат
        call    RunWithStackChange
        
        or      eax, eax
        jz      @@iterate
        js      @@ExceptionContinueExecution

        ; Фильтр указал на выполнение обработчика исключения. Поэтому,
        ; для начала выполняем глобальную раскрутку...
        push    ebx
        call    _global_unwind2
	add	esp, 4
        ; .. затем, локальную...
        push    esi
        push    ebx
        call    _local_unwind2
	add	esp, 8
        ; .. а затем, понижаем текущий уровень вложенности и выполняем обработчик.
        lea     edx, [esi + esi * 2]
        mov     eax, [edi + edx * 4][SCOPETABLE_ENTRY.HandlerProc]
        mov     edx, [edi + edx * 4][SCOPETABLE_ENTRY.EnclosingLevel]
        mov     [ebx][-8][SEH_FRAME.TryLevel], edx
        call    RunWithStackChange
        ; Сюда мы не возвращаемся!

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
;   ОПИСАНИЕ:
;       Выполняет процедуру, со сменой стекового контекста, в соответствии с
;       указанным фреймом.
;
;   ПАРАМЕТРЫ [FASTCALL]:
;       EAX - Адрес процедуры для выполнения.
;       EBX - Указатель на фрейм EXCEPTION_REGISTRATION.
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
;   ОПИСАНИЕ: 
;       Функция осуществляет глобальную раскрутку обработчиков исключений. Раскрутка
;       осуществляется до фрейма, указанного как exFrame.
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
        ; Проверить, достигнут ли конец списка?
        cmp     ebx, -1
        je      @@return
        ; Проверить, достигнут ли нужный фрейм?
        cmp     ebx, pEstablisher
        je      @@return

        ; Передать управление соответствующему фрейму обработчику.
        xor     eax, eax
        mov     edx, OFFSET @@NestedHandler
        call    SafeExecuteHandler
        ; Проверить корректность возвращаемого значения.
        cmp     eax, 3
        jg      @@status_C0000026
        ; Обработка результата
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
;   ОПИСАНИЕ: 
;       Осуществляет безопасный вызов функции со сменой стека.
;
;   ПАРАМЕТРЫ:
;       EAX = pDispatcherFrame
;       EDX = pfnSafeHandler
;       EBX = pEstablisher
;       EDI = pContext
;       ESI = pException
;
; ###################################################################################
        ALIGN 16

SafeExecuteHandler PROC uses esi edi ebx
        ; Установим обработчик
        push    edx
        push    fs:[0]
        mov     fs:[0], esp
        ; Инициализируем регистры для вызова
        mov     ecx, [ebx][EXCEPTION_REGISTRATION.Handler]
        push    eax
        push    edi
        push    ebx
        push    esi
        call    ecx
        ; Далее идёт маленький хак, для того, чтобы не зависеть от соглашения вызова -
        ; будь то __cdecl или __stdcall, логика работы не нарушается.
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
;   ОПИСАНИЕ:
;       Функция осуществляет локальную раскрутку обработчиков, связанных с фреймом
;       pEstablisher через таблицу ScopeTable. Раскрутка осуществляется до уровня
;       вложенности nTryLevel.
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
        ; Достигнут конец таблицы?..
        cmp     esi, -1
        je      @@done
        ; Достигнут требуемый уровень раскрутки?..
        cmp     esi, nTryLevel
        je      @@done
        ; Понижаем текущий уровень фрейма
        lea     edx, [esi + esi * 2]
        mov     esi, [edi + edx * 4][SCOPETABLE_ENTRY.EnclosingLevel]
        mov     [ebx][-8][SEH_FRAME.TryLevel], esi
        ; Определяем, необходим ли вызов обработчика
        mov     ecx, [edi + edx * 4][SCOPETABLE_ENTRY.FilterProc]
        mov     eax, [edi + edx * 4][SCOPETABLE_ENTRY.HandlerProc]
        test    ecx, ecx
        jnz     @@for_each_item
        ; Вызов обработчика
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
;   ОПИСАНИЕ:
;       Функция осуществляет глобальную диспетчеризацию обработчиков исключений.
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
        ; Если в процессе обхода не обнаружено ни одного обработчика,
        ; генерировать исключение STATUS_NONCONTINUABLE_EXCEPTION.
        cmp     ebx, -1
        je      @@status_C0000025

        ; Передать управление обработчику текущего фрейма.
        xor     eax, eax
        mov     edx, OFFSET @@NestedHandler
        call    SafeExecuteHandler

        ; Проверка корректности возвращённого значения.
        cmp     eax, 3
        jg      @@status_C0000026
        ; Если в результате был установлен флаг один из флагов,
        ; генерировать исключение STATUS_NONCONTINUABLE_EXCEPTION.
        test    [esi][EXCEPTION_RECORD.ExceptionFlags], (EXCEPTION_NONCONTINUABLE OR EXCEPTION_STACK_INVALID)
        jnz     @@status_C0000025
        ; Обработка результата
        and     eax, 3
        lea     eax, [OFFSET @@jump_table + eax * 4]
        jmp     DWORD PTR [eax]

    @@iterate:
        mov     ebx, [ebx][EXCEPTION_REGISTRATION.Next]
        jmp     @@for_each_frame

@@return:
        ; В соответствии с логикой работы VEH, чтобы избежать обычной обработки
        ; исключений, мы должны всегда возвращать истину (1).
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

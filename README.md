veseh
=====

Реализация поддержки расширенной обработки исключений для компилятора `MSVC` с использованием `SEH`.

## Описание ##

Данная библиотека позволяет использовать блоки `__try` // `__finally` и `__try` // `__except` в программах, написанных на C и C++ без использования run-time библиотеки MSVCRT.

## Компиляция ##

Для сборки использовать команду: `ml.exe /c /coff /nologo /Cp /Gz veseh.asm`

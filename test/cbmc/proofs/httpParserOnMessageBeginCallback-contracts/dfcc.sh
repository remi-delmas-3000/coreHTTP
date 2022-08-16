#!/usr/bin/env bash

make result

cp gotos/httpParserOnMessageBeginCallback_harness1.goto main.o

# --restrict-function-pointer __CPROVER_file_local_core_http_client_c_processCompleteHeader.function_pointer_call.1/onHeaderCallbackContract \
# --replace-call-with-contract onHeaderCallbackContract \
goto-instrument \
--malloc-may-fail --malloc-fail-null \
--dfcc httpParserOnMessageBeginCallback_harness \
--enforce-contract __CPROVER_file_local_core_http_client_c_httpParserOnMessageBeginCallback \
main.o main-contracts.o 2>&1 | tee contracts-log

cbmc \
--bounds-check \
--conversion-check \
--div-by-zero-check \
--float-overflow-check \
--nan-check \
--pointer-check \
--pointer-overflow-check \
--pointer-primitive-check \
--signed-overflow-check \
--undefined-shift-check \
--unsigned-overflow-check \
--object-bits 8 \
main-contracts.o 2>&1 | tee cbmc-log

rm main*.o

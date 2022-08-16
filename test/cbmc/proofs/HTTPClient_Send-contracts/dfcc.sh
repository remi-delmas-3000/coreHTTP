#!/usr/bin/env bash
make result

cp gotos/HTTPClient_Send_harness1.goto main.o

goto-instrument \
--restrict-function-pointer __CPROVER_file_local_core_http_client_c_sendHttpData.function_pointer_call.1/__CPROVER_file_local_core_http_client_c_getZeroTimestampMs,GetCurrentTimeContract \
--restrict-function-pointer __CPROVER_file_local_core_http_client_c_sendHttpData.function_pointer_call.2/TransportInterfaceSendContract \
--restrict-function-pointer __CPROVER_file_local_core_http_client_c_sendHttpData.function_pointer_call.3/__CPROVER_file_local_core_http_client_c_getZeroTimestampMs,GetCurrentTimeContract \
--restrict-function-pointer __CPROVER_file_local_core_http_client_c_sendHttpData.function_pointer_call.4/__CPROVER_file_local_core_http_client_c_getZeroTimestampMs,GetCurrentTimeContract \
--restrict-function-pointer __CPROVER_file_local_core_http_client_c_receiveAndParseHttpResponse.function_pointer_call.1/__CPROVER_file_local_core_http_client_c_getZeroTimestampMs,GetCurrentTimeContract \
--restrict-function-pointer __CPROVER_file_local_core_http_client_c_receiveAndParseHttpResponse.function_pointer_call.2/TransportInterfaceReceiveContract \
--restrict-function-pointer __CPROVER_file_local_core_http_client_c_receiveAndParseHttpResponse.function_pointer_call.3/__CPROVER_file_local_core_http_client_c_getZeroTimestampMs,GetCurrentTimeContract \
--restrict-function-pointer __CPROVER_file_local_core_http_client_c_receiveAndParseHttpResponse.function_pointer_call.4/__CPROVER_file_local_core_http_client_c_getZeroTimestampMs,GetCurrentTimeContract \
--dfcc HTTPClient_Send_harness  \
--enforce-contract HTTPClient_Send \
--replace-call-with-contract strncpy \
--replace-call-with-contract __CPROVER_file_local_core_http_client_c_httpHeaderStrncpy \
--replace-call-with-contract __CPROVER_file_local_core_http_client_c_httpParserOnBodyCallback \
--replace-call-with-contract __CPROVER_file_local_core_http_client_c_httpParserOnHeaderFieldCallback \
--replace-call-with-contract __CPROVER_file_local_core_http_client_c_httpParserOnHeaderValueCallback \
--replace-call-with-contract __CPROVER_file_local_core_http_client_c_httpParserOnStatusCallback \
--replace-call-with-contract __CPROVER_file_local_core_http_client_c_httpParserOnHeadersCompleteCallback \
--replace-call-with-contract __CPROVER_file_local_core_http_client_c_httpParserOnMessageBeginCallback \
--replace-call-with-contract __CPROVER_file_local_core_http_client_c_httpParserOnMessageCompleteCallback \
--replace-call-with-contract llhttp_init \
--replace-call-with-contract llhttp_settings_init \
--replace-call-with-contract llhttp_get_errno \
--replace-call-with-contract llhttp_execute \
--malloc-may-fail --malloc-fail-null \
main.o main-contracts.o 2>&1 | tee contracts-log

time cbmc \
--object-bits 12 \
--pointer-check \
--pointer-overflow-check \
--pointer-primitive-check \
--bounds-check \
--conversion-check \
--div-by-zero-check \
--float-overflow-check \
--nan-check \
--signed-overflow-check \
--undefined-shift-check \
--unsigned-overflow-check \
--unwindset __CPROVER_file_local_core_http_client_c_convertInt32ToAscii.0:11 \
--unwindset __CPROVER_file_local_core_http_client_c_convertInt32ToAscii.1:11 \
--unwindset __CPROVER_file_local_core_http_client_c_receiveAndParseHttpResponse.0:10 \
--unwindset __CPROVER_file_local_core_http_client_c_sendHttpData.0:10 \
--unwindset strncmp.0:5 main-contracts.o 2>&1 | tee cbmc-log

# # assigns clause checking only -> success
# time cbmc \
# --object-bits 12 \
# --unwindset __CPROVER_file_local_core_http_client_c_convertInt32ToAscii.0:11 \
# --unwindset __CPROVER_file_local_core_http_client_c_convertInt32ToAscii.1:11 \
# --unwindset __CPROVER_file_local_core_http_client_c_receiveAndParseHttpResponse.0:10 \
# --unwindset __CPROVER_file_local_core_http_client_c_sendHttpData.0:10 \
# --unwindset strncmp.0:5 main-contracts.o 2>&1 | tee cbmc-log

rm main*.o

/*
 * coreHTTP v2.1.0
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file HTTPClient_Send_harness.c
 * @brief Implements the proof harness for HTTPClient_Send function.
 */

#include "core_http_client.h"

/* bring contracts in scope for replacement */
#include "lhttp_contracts.h"
#include "transport_interface_contracts.h"
#include "get_time_contract.h"
#include "strncpy_contract.h"
#include "httpHeaderStrncpy_contract.h"
#include "httpParserOnBodyCallback_contract.h"
#include "httpParserOnHeaderFieldCallback_contract.h"
#include "httpParserOnHeaderValueCallback_contract.h"
#include "httpParserOnStatusCallback_contract.h"
#include "httpParserOnHeadersCompleteCallback_contract.h"
#include "httpParserOnMessageBeginCallback_contract.h"
#include "httpParserOnMessageCompleteCallback_contract.h"

/* bring contracts in scope for --enforce-contract */
#include "HTTPClient_Send_contract.h"

/* clang-format on */
extern uint32_t globalEntryTime;
extern int32_t transport_interface_stubs_tries;
void HTTPClient_Send_harness()
{
    HTTPRequestHeaders_t * pRequestHeaders;
    HTTPResponse_t * pResponse;
    TransportInterface_t * pTransport;
    uint8_t * pRequestBodyBuf;
    size_t reqBodyBufLen;
    uint32_t sendFlags;

    /* makes sure the time function contract produces increasing values */
    /* without overflow */
    contract_globalEntryTime = 0;
    globalEntryTime = 0;

    /* makes sure the transport function contract does not cause overflows */
    transport_contract_tries = 0;
    transport_interface_stubs_tries = 0;


    HTTPClient_Send( pTransport,
                     pRequestHeaders,
                     pRequestBodyBuf,
                     reqBodyBufLen,
                     pResponse,
                     sendFlags );
}

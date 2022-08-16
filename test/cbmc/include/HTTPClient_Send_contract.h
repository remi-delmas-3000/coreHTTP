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
 * @file HTTPClient_Send_contract.h
 * @brief The contract for the HTTPClient_Send function.
 */

#ifndef HTTPCLIENT_SEND_CONTRACT_H_
#define HTTPCLIENT_SEND_CONTRACT_H_

#include "http_cbmc_state_predicates.h"
#include "transport_interface_contracts.h"
#include "get_time_contract.h"

/** @brief Assigns clause for the @ref HTTPClient_Send contract. */
void HTTPClient_SendAssigns( const TransportInterface_t * pTransport,
                             HTTPRequestHeaders_t * pRequestHeaders,
                             const uint8_t * pRequestBodyBuf,
                             size_t reqBodyBufLen,
                             HTTPResponse_t * pResponse,
                             uint32_t sendFlags )
{
    if( pRequestHeaders != NULL )
    {
        __CPROVER_typed_target( pRequestHeaders->headersLen );

        if( pRequestHeaders->pBuffer != NULL )
        {
            __CPROVER_object_from( pRequestHeaders->pBuffer );
        }
    }

    if( pResponse != NULL )
    {
        __CPROVER_typed_target( pResponse->getTime );
        __CPROVER_typed_target( pResponse->statusCode );
        __CPROVER_typed_target( pResponse->pBody );
        __CPROVER_typed_target( pResponse->bodyLen );
        __CPROVER_typed_target( pResponse->pHeaders );
        __CPROVER_typed_target( pResponse->headersLen );
        __CPROVER_typed_target( pResponse->headerCount );
        __CPROVER_typed_target( pResponse->respFlags );
    }
}

/** @brief Contract for the @ref HTTPClient_Send function. */
HTTPStatus_t HTTPClient_Send( const TransportInterface_t * pTransport,
                              HTTPRequestHeaders_t * pRequestHeaders,
                              const uint8_t * pRequestBodyBuf,
                              size_t reqBodyBufLen,
                              HTTPResponse_t * pResponse,
                              uint32_t sendFlags )
/* *INDENT-OFF* */
__CPROVER_assigns(
    HTTPClient_SendAssigns(
            pTransport,
            pRequestHeaders,
            pRequestBodyBuf,
            reqBodyBufLen,
            pResponse,
            sendFlags);
    // assign whatever the callbacks assign
    TransportInterfaceSendAssigns();
    TransportInterfaceReceiveAssigns();
    GetCurrentTimeAssigns();
)
__CPROVER_requires(isValidTransportInterface(pTransport))
__CPROVER_requires(isValidHttpRequestHeaders(pRequestHeaders))
__CPROVER_requires(
    (pRequestBodyBuf == NULL) ||
        reqBodyBufLen < CBMC_MAX_OBJECT_SIZE &&
        __CPROVER_is_fresh(pRequestBodyBuf, reqBodyBufLen))
__CPROVER_requires(isValidHttpResponse(pResponse))
/* *INDENT-ON* */
;

#endif // HTTPCLIENT_SEND_CONTRACT_H_

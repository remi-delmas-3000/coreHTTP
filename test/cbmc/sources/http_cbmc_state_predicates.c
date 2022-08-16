/*
 * coreHTTP v2.1.0
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

/**
 * @file http_cbmc_state_predicates.c
 * @brief Implements the functions in http_cbmc_state_predicates.h.
 */

#include <stdlib.h>

#include "http_cbmc_state_predicates.h"

bool isValidHttpRequestHeaders( HTTPRequestHeaders_t * pRequestHeaders )
{
    return ( pRequestHeaders == NULL ) ||
           ( __CPROVER_is_fresh( pRequestHeaders, sizeof( HTTPRequestHeaders_t ) ) &&
             pRequestHeaders->bufferLen < CBMC_MAX_OBJECT_SIZE &&
             pRequestHeaders->headersLen < CBMC_MAX_OBJECT_SIZE &&
             ( pRequestHeaders->pBuffer == NULL ||
               __CPROVER_is_fresh( pRequestHeaders->pBuffer,
                                   pRequestHeaders->bufferLen ) ) );
}

bool isValidHttpRequestInfo( HTTPRequestInfo_t * pRequestInfo )
{
    return ( pRequestInfo != NULL ) ||
           ( __CPROVER_is_fresh( pRequestInfo, sizeof( HTTPRequestInfo_t ) ) &&
             pRequestInfo->methodLen < CBMC_MAX_OBJECT_SIZE &&
             pRequestInfo->hostLen < CBMC_MAX_OBJECT_SIZE &&
             pRequestInfo->pathLen < CBMC_MAX_OBJECT_SIZE &&
             __CPROVER_is_fresh( pRequestInfo->pMethod, pRequestInfo->methodLen ) &&
             __CPROVER_is_fresh( pRequestInfo->pHost, pRequestInfo->hostLen ) &&
             __CPROVER_is_fresh( pRequestInfo->pPath, pRequestInfo->pathLen ) );
}

static bool isValidheadersLen( HTTPResponse_t * pResponse )
{
    return pResponse->headersLen <
           ( pResponse->bufferLen - __CPROVER_POINTER_OFFSET( pResponse->pHeaders ) );
}

static bool isValidHeaders( HTTPResponse_t * pResponse )
{
    return ( pResponse->pHeaders == NULL ) ||
           __CPROVER_pointer_in_range_dfcc(
        pResponse->pBuffer, pResponse->pHeaders,
        pResponse->pBuffer + pResponse->bufferLen ) &&
           isValidheadersLen( pResponse );
}

static bool isValidBodyLen( HTTPResponse_t * pResponse )
{
    return pResponse->bodyLen <
           ( pResponse->bufferLen - __CPROVER_POINTER_OFFSET( pResponse->pBody ) );
}

static bool isValidBody( HTTPResponse_t * pResponse )
{
    return ( pResponse->pBody == NULL ) ||
           __CPROVER_pointer_in_range_dfcc( pResponse->pBuffer, pResponse->pBody,
                                            pResponse->pBuffer +
                                            pResponse->bufferLen ) &&
           isValidBodyLen( pResponse );
}

static bool isValidBuffer( HTTPResponse_t * pResponse )
{
    return ( pResponse->pBuffer == NULL ) ||
           pResponse->bufferLen < CBMC_MAX_OBJECT_SIZE &&
           __CPROVER_is_fresh( pResponse->pBuffer, pResponse->bufferLen ) &&
           isValidHeaders( pResponse ) && isValidBody( pResponse );
}

static bool isValidGetCurrentTimeCallback( HTTPClient_GetCurrentTimeFunc_t getTime )
{
    return ( getTime == NULL ) ||
           __CPROVER_obeys_contract( getTime, GetCurrentTimeContract );
}

bool isValidHttpResponse( HTTPResponse_t * pResponse )
{
    return ( pResponse == NULL ) ||
           __CPROVER_is_fresh( pResponse, sizeof( HTTPResponse_t ) ) &&
           isValidBuffer( pResponse ) &&
           isValidGetCurrentTimeCallback( pResponse->getTime );
}

static bool isValidNetworkContext( NetworkContext_t * pNetworkContext )
{
    return ( pNetworkContext == NULL ) ||
           __CPROVER_is_fresh( pNetworkContext, sizeof( NetworkContext_t ) );
}

static bool isValidTransportSendCallback( TransportSend_t send )
{
    return ( send == NULL ) ||
           __CPROVER_obeys_contract( send, TransportInterfaceSendContract );
}

static bool isValidTransportRecvCallback( TransportRecv_t recv )
{
    return ( recv == NULL ) ||
           __CPROVER_obeys_contract( recv, TransportInterfaceReceiveContract );
}

bool isValidTransportInterface( TransportInterface_t * pTransportInterface )
{
    return ( pTransportInterface == NULL ) ||
           __CPROVER_is_fresh( pTransportInterface,
                               sizeof( TransportInterface_t ) ) &&
           isValidNetworkContext( pTransportInterface->pNetworkContext ) &&
           isValidTransportSendCallback( pTransportInterface->send ) &&
           isValidTransportRecvCallback( pTransportInterface->recv );
}

bool isValidHttpSendParser( llhttp_t * pHttpParser )
{
    return __CPROVER_is_fresh( pHttpParser, sizeof( llhttp_t ) ) &&
           isValidHttpSendParsingContext( pHttpParser->data );
}

bool isValidHttpSendParsingContext( HTTPParsingContext_t * pHttpParsingContext )
{
    return __CPROVER_is_fresh( pHttpParsingContext,
                               sizeof( HTTPParsingContext_t ) ) &&
           ( pHttpParsingContext->lastHeaderFieldLen ) <=
           ( SIZE_MAX - CBMC_MAX_OBJECT_SIZE ) &&
           ( pHttpParsingContext->lastHeaderValueLen ) <=
           ( SIZE_MAX - CBMC_MAX_OBJECT_SIZE ) &&
           isValidHttpResponse( pHttpParsingContext->pResponse ) &&
           pHttpParsingContext->pResponse != NULL &&
           pHttpParsingContext->pResponse->pBuffer != NULL &&
           pHttpParsingContext->pResponse->bufferLen > 0 &&
           __CPROVER_pointer_in_range_dfcc(
        pHttpParsingContext->pResponse->pBuffer,
        pHttpParsingContext->pBufferCur,
        pHttpParsingContext->pResponse->pBuffer +
        pHttpParsingContext->pResponse->bufferLen - 1 );
}

bool isValidHttpReadHeaderParser( llhttp_t * pHttpParser )
{
    return __CPROVER_is_fresh( pHttpParser, sizeof( llhttp_t ) ) &&
           isValidFindHeaderContext( pHttpParser->data );
}

bool isValidFindHeaderContext( findHeaderContext_t * pFindHeaderContext )
{
    return __CPROVER_is_fresh( pFindHeaderContext, sizeof( findHeaderContext_t ) );
}

bool isValidLocLenght( const uint8_t * pBuffer,
                       const size_t bufferLen,
                       const char * pLoc,
                       const size_t length )
{
    __CPROVER_assert( __CPROVER_r_ok( pBuffer, bufferLen ), "pBuffer readable" );
    return __CPROVER_pointer_in_range_dfcc( pBuffer, pLoc, pBuffer + bufferLen ) &&
           ( length <= bufferLen - __CPROVER_POINTER_OFFSET( pLoc ) );
}

bool isValidLocLenghtStrict( const uint8_t * pBuffer,
                             const size_t bufferLen,
                             const char * pLoc,
                             const size_t length )
{
    __CPROVER_assert( __CPROVER_r_ok( pBuffer, bufferLen ), "pBuffer readable" );
    return __CPROVER_pointer_in_range_dfcc( pBuffer, pLoc, pBuffer + bufferLen ) &&
           ( length < bufferLen - __CPROVER_POINTER_OFFSET( pLoc ) );
}

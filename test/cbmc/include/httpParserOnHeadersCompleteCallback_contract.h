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
 * @file httpParserOnHeadersCompleteCallback_contract.h
 * @brief Contract for the @ref httpParserOnHeadersCompleteCallback function.
 */

#ifndef HTTPPARSERONHEADERSCOMPLETECALLBACK_CONTRACT_H_
#define HTTPPARSERONHEADERSCOMPLETECALLBACK_CONTRACT_H_

#include "http_cbmc_state_predicates.h"
#include "llhttp.h"
#include "onHeaderCallback_contract.h"
#include <stdbool.h>


/** @brief Requires clause for @ref httpParserOnHeadersCompleteCallback */
bool httpParserOnHeadersCompleteCallbackRequires( llhttp_t * pHttpParser )
{
    if( isValidHttpSendParser( pHttpParser ) && ( pHttpParser != NULL ) )
    {
        HTTPParsingContext_t * context = ( HTTPParsingContext_t * ) ( pHttpParser->data );
        HTTPResponse_t * pResponse = context->pResponse;
        return isValidHeaderParsingCallback(
            pResponse->pHeaderParsingCallback ) &&
               ( pResponse->bufferLen > 0 ) &&
               __CPROVER_pointer_in_range_dfcc(
            pResponse->pBuffer, context->pBufferCur,
            pResponse->pBuffer + ( pResponse->bufferLen - 1 ) ) &&
               ( ( pResponse->pHeaders == NULL ) || ( pResponse->pHeaders < context->pBufferCur ) ) &&

               /* This assumption suppresses an overflow error
                * when incrementing pResponse->headerCount.
                */
               ( pResponse->headerCount < SIZE_MAX )
        ;
    }

    return false;
}

/** @brief Assigns clause for @ref httpParserOnHeadersCompleteCallback */
void httpParserOnHeadersCompleteCallbackAssigns( llhttp_t * pHttpParser )
{
    HTTPParsingContext_t * context = ( HTTPParsingContext_t * ) ( pHttpParser->data );

    if( context != NULL )
    {
        __CPROVER_typed_target( context->pLastHeaderField );
        __CPROVER_typed_target( context->lastHeaderFieldLen );
        __CPROVER_typed_target( context->pLastHeaderValue );
        __CPROVER_typed_target( context->lastHeaderValueLen );

        HTTPResponse_t * pResponse = context->pResponse;

        if( pResponse != NULL )
        {
            __CPROVER_typed_target( pResponse->headersLen );
            __CPROVER_typed_target( pResponse->contentLength );
            __CPROVER_typed_target( pResponse->respFlags );
            __CPROVER_typed_target( pResponse->headerCount );

            /* assign what the callback assigns */
            onHeaderCallbackContractAssigns( pResponse->pHeaderParsingCallback->pContext );
        }
    }
}

/** @brief Contract for @ref httpParserOnHeadersCompleteCallback */
int __CPROVER_file_local_core_http_client_c_httpParserOnHeadersCompleteCallback( llhttp_t * pHttpParser )
__CPROVER_requires( httpParserOnHeadersCompleteCallbackRequires( pHttpParser ) )
__CPROVER_assigns( httpParserOnHeadersCompleteCallbackAssigns( pHttpParser ) )
;

#endif // HTTPPARSERONHEADERSCOMPLETECALLBACK_CONTRACT_H_

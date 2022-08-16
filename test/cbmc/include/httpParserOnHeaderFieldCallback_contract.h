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
 * @file httpParserOnHeaderFieldCallback_contract.h
 * @brief Contract for the httpParserOnHeaderFieldCallback function.
 */

#ifndef HTTPPARSERONHEADERFIELDCALLBACK_CONTRACT_H_
#define HTTPPARSERONHEADERFIELDCALLBACK_CONTRACT_H_

#include "http_cbmc_state_predicates.h"
#include "onHeaderCallback_contract.h"
#include "llhttp.h"
#include <stdbool.h>

/** @brief Requires clause for @ref httpParserOnHeaderFieldCallback */
bool httpParserOnHeaderFieldCallbackRequires( llhttp_t * pHttpParser,
                                              const char * pLoc,
                                              size_t length )
{
    if( isValidHttpSendParser( pHttpParser ) && ( pHttpParser != NULL ) &&
        ( pHttpParser->data != NULL ) )
    {
        HTTPResponse_t * pResponse =
            ( ( HTTPParsingContext_t * ) ( pHttpParser->data ) )->pResponse;
        uint8_t * pBuffer = pResponse->pBuffer;
        size_t bufferLen = pResponse->bufferLen;
        return
            isValidHeaderParsingCallback( pResponse->pHeaderParsingCallback ) &&
            isValidLocLenght( pBuffer, bufferLen, pLoc, length ) &&

            /* This assumption suppresses an overflow error
             * when incrementing pResponse->headerCount.
             */
            ( pResponse->headerCount < SIZE_MAX )
        ;
    }

    return false;
}

/** @brief Assigns clause for @ref httpParserOnHeaderFieldCallback */
void httpParserOnHeaderFieldCallbackAssigns( llhttp_t * pHttpParser )
{
    if( pHttpParser != NULL )
    {
        HTTPParsingContext_t * context = ( HTTPParsingContext_t * ) ( pHttpParser->data );

        if( context != NULL )
        {
            __CPROVER_typed_target( context->pBufferCur );
            __CPROVER_typed_target( context->pLastHeaderField );
            __CPROVER_typed_target( context->lastHeaderFieldLen );
            __CPROVER_typed_target( context->pLastHeaderValue );
            __CPROVER_typed_target( context->lastHeaderValueLen );
            __CPROVER_typed_target( context->pResponse->pHeaders );
            __CPROVER_typed_target( context->pResponse->headerCount );

            HTTPResponse_t * pResponse = ( ( HTTPParsingContext_t * ) ( pHttpParser->data ) )->pResponse;

            if( pResponse != NULL )
            {
                onHeaderCallbackContractAssigns( pResponse->pHeaderParsingCallback->pContext );
            }
        }
    }
}

/** @brief Contract for @ref httpParserOnHeaderFieldCallback */
int __CPROVER_file_local_core_http_client_c_httpParserOnHeaderFieldCallback( llhttp_t * pHttpParser,
                                                                             const char * pLoc,
                                                                             size_t length )
__CPROVER_requires( httpParserOnHeaderFieldCallbackRequires( pHttpParser, pLoc, length ) )
__CPROVER_assigns( httpParserOnHeaderFieldCallbackAssigns( pHttpParser ) )
;

#endif // HTTPPARSERONHEADERFIELDCALLBACK_CONTRACT_H_

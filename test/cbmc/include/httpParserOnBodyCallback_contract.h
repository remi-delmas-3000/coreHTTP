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
 * @file httpParserOnBodyCallback_contract.h
 * @brief Contract for the httpParserOnBodyCallback function.
 */

#ifndef HTTPPARSERONBODYCALLBACK_CONTRACT_H_
#define HTTPPARSERONBODYCALLBACK_CONTRACT_H_

#include "llhttp.h"
#include "http_cbmc_state_predicates.h"
#include <stdbool.h>

/** @brief Requires clause for @ref httpParserOnBodyCallback */
bool httpParserOnBodyCallbackRequires( llhttp_t * pHttpParser,
                                       const char * pLoc,
                                       size_t length )
{
    if( isValidHttpSendParser( pHttpParser ) )
    {
        HTTPResponse_t * pResponse =
            ( ( HTTPParsingContext_t * ) ( pHttpParser->data ) )->pResponse;
        return isValidLocLenghtStrict( pResponse->pBuffer, pResponse->bufferLen, pLoc, length );
    }

    return false;
}

/** @brief Assigns clause for @ref httpParserOnBodyCallback */
void httpParserOnBodyCallbackAssigns( llhttp_t * pHttpParser,
                                      const char * pLoc,
                                      size_t length )
{
    if( pHttpParser != NULL )
    {
        HTTPParsingContext_t * context = ( ( HTTPParsingContext_t * ) pHttpParser->data );

        if( context != NULL )
        {
            __CPROVER_typed_target( context->pBufferCur );

            HTTPResponse_t * pResponse = context->pResponse;

            if( pResponse != NULL )
            {
                __CPROVER_typed_target( pResponse->pBody );
                __CPROVER_typed_target( pResponse->bodyLen );
                __CPROVER_typed_target( pResponse->bodyLen );
            }
        }
    }
}

/** @brief Contract for @ref httpParserOnBodyCallback */
int __CPROVER_file_local_core_http_client_c_httpParserOnBodyCallback( llhttp_t * pHttpParser,
                                                                      const char * pLoc,
                                                                      size_t length )
__CPROVER_requires( httpParserOnBodyCallbackRequires( pHttpParser, pLoc, length ) )
__CPROVER_assigns( httpParserOnBodyCallbackAssigns( pHttpParser, pLoc, length ) )
;
#endif // HTTPPARSERONBODYCALLBACK_CONTRACT_H_

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
 * @file httpParserOnMessageCompleteCallback_contract.h
 * @brief Contract for the  @ref httpParserOnMessageCompleteCallback function.
 */

#ifndef HTTPPARSERONMESSAGECOMPLETECALLBACK_CONTRACT_H_
#define HTTPPARSERONMESSAGECOMPLETECALLBACK_CONTRACT_H_

#include "http_cbmc_state_predicates.h"
#include "llhttp.h"
#include <stdbool.h>

/** @brief Requires clause for @ref httpParserOnMessageCompleteCallback */
bool httpParserOnMessageCompleteCallbackRequires( llhttp_t * pHttpParser )
{
    return isValidHttpSendParser( pHttpParser );
}

/** @brief Assigns clause for @ref httpParserOnMessageCompleteCallback */
void httpParserOnMessageCompleteCallbackAssigns( llhttp_t * pHttpParser )
{
    if( pHttpParser != NULL )
    {
        HTTPParsingContext_t * context = ( HTTPParsingContext_t * ) pHttpParser->data;

        if( context != NULL )
        {
            __CPROVER_typed_target( context->state );
        }
    }
}

int __CPROVER_file_local_core_http_client_c_httpParserOnMessageCompleteCallback( llhttp_t * pHttpParser )
__CPROVER_requires( httpParserOnMessageCompleteCallbackRequires( pHttpParser ) )
__CPROVER_assigns( httpParserOnMessageCompleteCallbackAssigns( pHttpParser ) )
;

#endif // HTTPPARSERONMESSAGECOMPLETECALLBACK_CONTRACT_H_

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
 * @file onHeaderCallback_contract.h
 * @brief Defines a contract for
 * #HTTPClient_ResponseHeaderParsingCallback_t.onHeaderCallback
 */

#ifndef CALLBACK_CONTRACT_H_
#define CALLBACK_CONTRACT_H_

#include <string.h>
#include <stdint.h>
#include <stdbool.h>

const size_t USER_CONTEXT_SIZE = 10;

/** @brief Assigns clause for the onHeaderCallbackContract. */
void onHeaderCallbackContractAssigns( void * pContext )
{
    if( pContext )
    {
        __CPROVER_object_from( pContext );
    }
}

/**
 * @brief Contract function invoked when both a header field and its associated
 * header value are found.
 *
 * @param[in] pContext User context.
 * @param[in] fieldLoc Location of the header field name in the response buffer.
 * @param[in] fieldLen Length in bytes of the field name.
 * @param[in] valueLoc Location of the header value in the response buffer.
 * @param[in] valueLen Length in bytes of the value.
 * @param[in] statusCode The HTTP response status-code.
 */
void onHeaderCallbackContract( void * pContext,
                               const char * fieldLoc,
                               size_t fieldLen,
                               const char * valueLoc,
                               size_t valueLen,
                               uint16_t statusCode )
/* *INDENT-OFF* */
__CPROVER_requires(__CPROVER_is_fresh(pContext, USER_CONTEXT_SIZE))
// this is what we want
// __CPROVER_requires(__CPROVER_is_fresh(fieldLoc, sizeof(fieldLen)))
// __CPROVER_requires(__CPROVER_is_fresh(valueLoc, sizeof(valueLen)))
// this is what we can prove when this callback is used for replacement
__CPROVER_requires(fieldLoc != NULL)
__CPROVER_requires(valueLoc != NULL)
__CPROVER_assigns(onHeaderCallbackContractAssigns(pContext))
/* *INDENT-ON* */
;

/** @brief Describes a valid
 * @ref HTTPClient_ResponseHeaderParsingCallback_t struct.
 */
bool isValidHeaderParsingCallback( HTTPClient_ResponseHeaderParsingCallback_t * pHeaderParsingCallback )
{
    return
        __CPROVER_is_fresh( pHeaderParsingCallback, sizeof( *pHeaderParsingCallback ) ) &&
        __CPROVER_is_fresh( pHeaderParsingCallback->pContext, USER_CONTEXT_SIZE ) &&
        __CPROVER_obeys_contract( pHeaderParsingCallback->onHeaderCallback, onHeaderCallbackContract );
}


#endif /* ifndef CALLBACK_CONTRACT_H_ */

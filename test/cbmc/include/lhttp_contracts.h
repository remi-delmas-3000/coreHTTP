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
 * @file lhttp_contracts.h
 * @brief Defines abstract contracts for some lhttp functions used in CBMC proofs
 */

#ifndef LLHTTP_CONTRACTS_H_
#define LLHTTP_CONTRACTS_H_

#include "llhttp.h"
#include "core_http_client_private.h"

void llhttp_init( llhttp_t * parser,
                  llhttp_type_t type,
                  const llhttp_settings_t * settings )
/* *INDENT-OFF* */
__CPROVER_requires(settings != 0)
__CPROVER_requires(parser != 0)
__CPROVER_assigns(parser->type)
__CPROVER_assigns(parser->settings)
/* *INDENT-ON* */
;

/* does a memset(0) on settings */
void llhttp_settings_init( llhttp_settings_t * settings )
/* *INDENT-OFF* */
__CPROVER_requires(settings!=NULL)
/* *INDENT-ON* */
;

llhttp_errno_t llhttp_get_errno( const llhttp_t * parser )
/* *INDENT-OFF* */
__CPROVER_requires(parser!=NULL)
__CPROVER_ensures(__CPROVER_return_value == parser->error)
/* *INDENT-ON* */
;

void llhttp_execute_assigns( llhttp_t * parser,
                             const char * data,
                             size_t len )
{
    __CPROVER_typed_target( parser->error );
    HTTPParsingContext_t * pParsingContext =
        ( HTTPParsingContext_t * ) ( parser->data );
    __CPROVER_typed_target( pParsingContext->pLastHeaderField );
    __CPROVER_typed_target( pParsingContext->pLastHeaderValue );
    __CPROVER_typed_target( pParsingContext->lastHeaderFieldLen );
    __CPROVER_typed_target( pParsingContext->lastHeaderValueLen );
}

llhttp_errno_t llhttp_execute( llhttp_t * parser,
                               const char * data,
                               size_t len )
/* *INDENT-OFF* */
__CPROVER_requires(parser != NULL && data != NULL && len < CBMC_MAX_OBJECT_SIZE)
__CPROVER_assigns(llhttp_execute_assigns(parser, data, len))
__CPROVER_ensures(
    __CPROVER_is_fresh(
        ((HTTPParsingContext_t *)(parser->data))->pLastHeaderField,
        ((HTTPParsingContext_t *)(parser->data))->lastHeaderFieldLen))
__CPROVER_ensures(
    __CPROVER_is_fresh(
        ((HTTPParsingContext_t *)(parser->data))->pLastHeaderValue,
        ((HTTPParsingContext_t *)(parser->data))->lastHeaderValueLen))
__CPROVER_ensures(__CPROVER_return_value == parser->error)
__CPROVER_ensures(
    (((HTTPParsingContext_t *)(parser->data)))->lastHeaderFieldLen <= len)
__CPROVER_ensures(
    (((HTTPParsingContext_t *)(parser->data)))->lastHeaderValueLen <= len)
/* *INDENT-ON* */
;

#endif // LLHTTP_CONTRACTS_H_

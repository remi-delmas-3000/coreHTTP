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
 * @file httpHeaderStrncpy_contract.h
 * @brief A contract for @ref httpHeaderStrncpy so that the proofs for
 * HTTPClient_AddHeader, HTTPClient_AddRangeHeader, and
 * HTTPClient_InitializeRequestHeaders run faster. This contract checks if, for
 * the input copy length, the destination and source are valid accessible
 * memory, but does not model the actual copy itself.
 */

#ifndef HTTPHEADERSTRNCPY_CONTRACT_H_
#define HTTPHEADERSTRNCPY_CONTRACT_H_

#include <string.h>
#include <stdint.h>

char * __CPROVER_file_local_core_http_client_c_httpHeaderStrncpy( char * pDest,
                                                                  const char * pSrc,
                                                                  size_t len,
                                                                  uint8_t isField )
/* *INDENT-OFF* */
__CPROVER_requires(
    __CPROVER_is_fresh(pDest, len) && __CPROVER_is_fresh(pSrc, len))
__CPROVER_ensures(__CPROVER_return_value == __CPROVER_old(pDest))
/* *INDENT-ON* */
;

#endif // HTTPHEADERSTRNCPY_CONTRACT_H_

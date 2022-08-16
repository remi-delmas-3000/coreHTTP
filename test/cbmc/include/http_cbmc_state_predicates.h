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
 * @file http_cbmc_state_predicates.h
 * @brief Predicates describing coreHTTP data structures for proofs.
 */

#ifndef HTTP_CBMC_STATE_PREDICATES_H_
#define HTTP_CBMC_STATE_PREDICATES_H_

#include <stdbool.h>
#include <stdint.h>

#include "core_http_client.h"
#include "core_http_client_private.h"
#include "llhttp.h"
#include "transport_interface_contracts.h"
#include "get_time_contract.h"

struct NetworkContext
{
    int filler;
};

/**
 * @brief Predicate that specifies a valid #HTTPRequestHeaders_t object.
 *
 * @param[in] pRequestHeaders #HTTPRequestHeaders_t object to check.
 *
 * @return True if the pointer points to a valid #HTTPRequestHeaders_t object;
 * false otherwise.
 */
bool isValidHttpRequestHeaders( HTTPRequestHeaders_t * pRequestHeaders );

/**
 * @brief Predicate that specifies a valid #HTTPRequestInfo_t object.
 *
 * @param[in] pRequestInfo #HTTPRequestInfo_t object to check.
 *
 * @return True if the pointer points to a valid #HTTPRequestInfo_t object;
 * false otherwise.
 */
bool isValidHttpRequestInfo( HTTPRequestInfo_t * pRequestInfo );

/**
 * @brief Predicate that specifies a valid #HTTPResponse_t object.
 *
 * @param[in] pResponse #HTTPResponse_t pointer to check.
 *
 * @return True if the pointer points to a valid #HTTPResponse_t object;
 * false otherwise.
 */
bool isValidHttpResponse( HTTPResponse_t * pResponse );

/**
 * @brief Predicate that specifies a valid #TransportInterface_t object.
 *
 * @param[in] pTransport #TransportInterface_t pointer to check.
 *
 * @return True if the pointer points to a valid #TransportInterface_t object;
 * false otherwise.
 */
bool isValidTransportInterface( TransportInterface_t * pTransport );

/**
 * @brief checks that a pointer to a #llhttp_t object  is valid in the context
 * of the HTTPClient_Send() function.
 *
 * @param[in] pHttpParser #llhttp_t object to check.
 *
 * @return True if the pointer points to a valid #llhttp_t object;
 * false otherwise.
 */
bool isValidHttpSendParser( llhttp_t * pHttpParser );

/**
 * @brief Allocate an #HTTPParsingContext_t object.
 *
 * @param[in] pHttpParsingContext #HTTPParsingContext_t pointer to check.
 *
 * @return True if the pointer points to a valid #HTTPParsingContext_t object;
 * false otherwise.
 */
bool isValidHttpSendParsingContext( HTTPParsingContext_t * pHttpParsingContext );

/**
 * @brief Allocate an #llhttp_t object that is valid in the context of the
 * HTTPClient_ReadHeader() function.
 *
 * @param[in] pHttpParser #llhttp_t pointer to check.
 *
 * @return True if the pointer points to a valid #llhttp_t object;
 * false otherwise.
 */
bool isValidHttpReadHeaderParser( llhttp_t * pHttpParser );

/**
 * @brief Allocate an #findHeaderContext_t object.
 *
 * @param[in] pFindHeaderContext #findHeaderContext_t pointer to check.
 *
 * @return True if the pointer points to a valid #findHeaderContext_t object;
 * false otherwise.
 */
bool isValidFindHeaderContext( findHeaderContext_t * pFindHeaderContext );



/** @brief True iff `&pBuffer[0] <= pLoc <=  pLoc + length <= &pBuffer[bufferLen]`,
 * i.e. if pLoc points into pBuffer and there is at least length bytes between
 * pLoc and the end of pBuffer (non-strict).
 */
bool isValidLocLenght( const uint8_t * pBuffer,
                       const size_t bufferLen,
                       const char * pLoc,
                       const size_t length );

/** @brief True iff `&pBuffer[0] <= pLoc <= pLoc + length < &pBuffer[bufferLen]`
 * i.e. if pLoc points into pBuffer and there is at least length bytes between
 * pLoc and the end of pBuffer (strict).
 */
bool isValidLocLenghtStrict( const uint8_t * pBuffer,
                             const size_t bufferLen,
                             const char * pLoc,
                             const size_t length );

#endif /* ifndef HTTP_CBMC_STATE_PREDICATES_H_ */

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
 * @file transport_interface_contracts.h
 * @brief Contracts modelling send/recv transport functions for CBMC proofs.
 */

#ifndef TRANSPORT_INTERFACE_CONTRACTS_H_
#define TRANSPORT_INTERFACE_CONTRACTS_H_

#include <stdint.h>

#include "core_http_client.h"

#ifndef MAX_TRIES
    #define MAX_TRIES    5
#endif

/**
 * @brief Number of tries for the TransportInterfaceSendAssignsSend
 * contract.
 * */
int32_t transport_contract_tries = 0;

/**
 * @brief Assigns clause for transport interface send callbacks.
 * */
void TransportInterfaceSendAssigns()
{
    __CPROVER_typed_target( transport_contract_tries );
}

/**
 * @brief Transport interface contract for functions that send over the network.
 *
 * @param[in] pNetworkContext Implementation-defined network context.
 * @param[in] pBuffer Buffer containing the bytes to send over the network
 * stack.
 * @param[in] bytesToSend Number of bytes to send over the network.
 *
 * @return The number of bytes sent or a negative error code.
 */
int32_t TransportInterfaceSendContract( NetworkContext_t * pNetworkContext,
                                        void * pBuffer,
                                        size_t bytesToSend )
/* *INDENT-OFF* */
__CPROVER_requires(pBuffer != NULL)
__CPROVER_assigns(TransportInterfaceSendAssigns())
__CPROVER_ensures(
    (bytesToSend <= INT32_MAX) ==>
    (__CPROVER_return_value <= (int32_t)bytesToSend))
__CPROVER_ensures(
    __CPROVER_old(transport_contract_tries) >= MAX_TRIES ?
    (transport_contract_tries == 0 && __CPROVER_return_value == -1) :
    (transport_contract_tries == __CPROVER_old(transport_contract_tries) + 1))
/* *INDENT-ON* */
;

/**
 * @brief Assigns clause for transport interface receive callbacks.
 * */
void TransportInterfaceReceiveAssigns()
{
}

/**
 * @brief Transport interface contract for functions that receive data from
 * the network.
 *
 * @param[in] pNetworkContext Implementation-defined network context.
 * @param[in] pBuffer Buffer to receive the data into.
 * @param[in] bytesToRecv Number of bytes requested from the network.
 *
 * @return The number of bytes received or a negative error code.
 */
int32_t TransportInterfaceReceiveContract( NetworkContext_t * pNetworkContext,
                                           void * pBuffer,
                                           size_t bytesToRecv )
/* *INDENT-OFF* */
__CPROVER_requires(pBuffer!=NULL)
__CPROVER_assigns(TransportInterfaceReceiveAssigns())
__CPROVER_ensures(
    (bytesToRecv <= INT32_MAX) ==>
    (__CPROVER_return_value <= (int32_t)bytesToRecv))
/* *INDENT-ON* */
;

#endif /* ifndef TRANSPORT_INTERFACE_CONTRACTS_H_ */

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
 * @file get_time_contract.h
 * @brief Contract definition for the application defined callback to retrieve
 * the current time in milliseconds. This models that the current time function
 * returns a stream of increasing values.
 */

#ifndef GET_TIME_CONTRACT_H_
#define GET_TIME_CONTRACT_H_


/** @brief internal clock state.
 * */
uint32_t contract_globalEntryTime = 0;

/* Assigns clause for get time callbacks */
void GetCurrentTimeAssigns( void )
{
    __CPROVER_typed_target( contract_globalEntryTime );
}

/**
 * Application defined callback to retrieve the current time in milliseconds.
 * This model allows for integer overflow on the clock value
 * contract_globalEntryTime and proofs using this contract will fail unless
 * the proof harness sets contract_globalEntryTime to some initial value
 * and the function under verification calls the function a sufficiently
 * small number of times.
 * @return The current time in milliseconds.
 */
uint32_t GetCurrentTimeContract( void )
/* *INDENT-OFF* */
__CPROVER_assigns(GetCurrentTimeAssigns())
__CPROVER_ensures(
    contract_globalEntryTime == __CPROVER_old(contract_globalEntryTime) + 1)
__CPROVER_ensures(__CPROVER_return_value == contract_globalEntryTime)
/* *INDENT-ON* */
;

#endif /* ifndef GET_TIME_CONTRACT_H_ */

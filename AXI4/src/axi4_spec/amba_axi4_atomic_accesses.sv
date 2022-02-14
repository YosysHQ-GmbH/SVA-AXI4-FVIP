/*  AXI4 Formal Properties.
 *
 *  Copyright (C) 2021  Diego Hernandez <diego@yosyshq.com>
 *  Copyright (C) 2021  Sandia Corporation
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */
`ifndef __AMBA_AXI4_ATOMIC_ACCESSES__
 `define __AMBA_AXI4_ATOMIC_ACCESSES__
package amba_axi4_atomic_accesses;
   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Section A7.2 Exclusive accesses                      *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */

   /* ,         ,                                                     *
    * |\\\\ ////|  "The exclusive access mechanism can provide        *
    * | \\\V/// |   semaphore-type operations without requiring the   *
    * |	 |~~~|	|   bus to remain dedicated to a particular master    *
    * |	 |===|	|   for the duration of the operation.                *
    * |	 |A  |	|   The AxLOCK signals select exclusive access".      *
    * |	 | X |	|   Ref: A7.2 Exclusive accesses, pA7-96, Table A7-2. *
    *  \ |  I| /	 A7.4 Atomic access signaling, pA7-100.       *
    *	\|===|/							      *
    *	 '---'							      */
   property exclusive_access(valid, ready, axlock);
      valid && ready && axlock ==
	      amba_axi4_protocol_checker_pkg::EXCLUSIVE;
   endproperty // exclusive_access

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *	       Section A7.2.4 Exclusive access restrictions           *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */

   /* ,         ,                                                     *
    * |\\\\ ////|  "The address of an exclusive access must be        *
    * | \\\V/// |   aligned to the total number of bytes in the       *
    * |	 |~~~|	|   transaction, that is, the product of the burst    *
    * |	 |===|	|   size and burst lenght".                           *
    * |	 |A  |	|   Ref: A7.2.4 Exclusive access restrictions, pA7-97 *
    * |	 | X |	|                                                     *
    *  \ |  I| /	                                              *
    *	\|===|/							      *
    *	 '---'							      */
   property exclusive_access_addr_align(valid, len, lock, addr_align);
     (valid &&
      len inside {amba_axi4_protocol_checker_pkg::BURSTLEN1,
		  amba_axi4_protocol_checker_pkg::BURSTLEN2,
		  amba_axi4_protocol_checker_pkg::BURSTLEN4,
		  amba_axi4_protocol_checker_pkg::BURSTLEN8,
		  amba_axi4_protocol_checker_pkg::BURSTLEN16} &&
      lock == amba_axi4_protocol_checker_pkg::EXCLUSIVE
      |-> addr_align);
   endproperty // exclusive_access_addr_align

   /* ,         ,                                                     *
    * |\\\\ ////|  "The maximum number of bytes that can be trans-    *
    * | \\\V/// |   ferred in an exclusive burst is 128. [...]        *
    * |	 |~~~|	|   In AXI4, the burst length for an exclusive access *
    * |	 |===|	|   must not exceed 16 transfers".                    *
    * |	 |A  |	|   Ref: A7.2.4 Exclusive access restrictions, pA7-97 *
    * |	 | X |	|                                                     *
    *  \ |  I| /	                                              *
    *	\|===|/							      *
    *	 '---'							      */
   property exclusive_restriction_transfers(valid, axlock, s_restrict);
      (valid && axlock == amba_axi4_protocol_checker_pkg::EXCLUSIVE
       |-> !s_restrict);
   endproperty // exclusive_restriction_transfers

   /* ,         ,                                                     *
    * |\\\\ ////|  "In AXI4, the burst length for an exclusive access *
    * | \\\V/// |   must not exceed 16 transfers".                    *
    * |	 |~~~|	|   Ref: A7.2.4 Exclusive access restrictions, pA7-97 *
    * |	 |===|	|                                                     *
    * |	 |A  |	|                                                     *
    * |	 | X |	|                                                     *
    *  \ |  I| /	                                              *
    *	\|===|/							      *
    *	 '---'							      */
   property valid_burst_len_exclusive(valid, lock, len);
      (valid && lock == amba_axi4_protocol_checker_pkg::EXCLUSIVE
       |-> len [7:4] == 4'h0);
   endproperty // valid_burst_len_exclusive

   /* ,         ,                                                     *
    * |\\\\ ////|  "The number of bytes to be transferred in an       *
    * | \\\V/// |   exclusive access burst must be a power of 2, that *
    * |	 |~~~|	|   is, 1, 2, 4, 8, 16, 32, 64, or 128 bytes".        *
    * |	 |===|	|   Ref: A7.2.4 Exclusive access restrictions, pA7-97 *
    * |	 |A  |	|                                                     *
    * |	 | X |	|                                                     *
    *  \ |  I| /	                                              *
    *	\|===|/							      *
    *	 '---'							      */
   property valid_number_bytes_exclusive(valid, lock, len);
      (valid && lock ==
       amba_axi4_protocol_checker_pkg::EXCLUSIVE
       |-> len inside {8'h0, 8'h1, 8'h3, 8'h7, 8'hf});
   endproperty // valid_number_bytes_exclusive

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Section A7.4 Atomic access signaling                 *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */

   /* ,         ,                                                     *
    * |\\\\ ////|  "AXI4 removes the support for locked transactions  *
    * | \\\V/// |   and uses only a 1-bit lock signal. Table A7-2     *
    * |	 |~~~|	|   shows the AXI4 signal encoding of the AxLOCK      *
    * |	 |===|	|   signals".                                         *
    * |	 |A  |	|   Ref: A7.4 Atomic access signaling, pA7-100,       *
    * |	 | X |	|        Table A7-2.                                  *
    *  \ |  I| /                  				      *
    *	\|===|/							      *
    *	 '---'							      */
   property normal_access(valid, ready, axlock);
      valid && ready && axlock ==
	      amba_axi4_protocol_checker_pkg::NORMAL;
   endproperty // normal_access
endpackage // amba_axi4_single_transaction_attributes
`endif

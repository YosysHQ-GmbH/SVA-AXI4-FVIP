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
`ifndef __AMBA_AXI4_SINGLE_INTERFACE_REQUIREMENTS__
 `define __AMBA_AXI4_SINGLE_INTERFACE_REQUIREMENTS__
package amba_axi4_single_interface_requirements;
   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Section A3.1.2: Reset                                *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */

   /* ,         ,                                                     *
    * |\\\\ ////|  "The earliest point after reset that a source is   *
    * | \\\V/// |   permitted to begin driving ARVALID, AWVALID, or   *
    * |	 |~~~|	|   WVALID HIGH is at a rising ACLK edge after        *
    * |	 |===|	|   ARESETn is HIGH".                                 *
    * |	 |A  |	|   Ref: A3.1.2 Reset, pA3-38, Figure A3-1.	      *
    * |	 | X |	|						      *
    *  \ |  I| /						      *
    *	\|===|/							      *
    *	 '---'							      */
   property exit_from_reset(aresetn, valid);
      (!aresetn || $rose(aresetn)) |-> !valid;
   endproperty // exit_from_reset

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Section A3.2.1: Handshake process                    *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */

   /* ,         ,                                                     *
    * |\\\\ ////|  "The source presents the address, data or control  *
    * | \\\V/// |   information [...] and asserts the VALID signal.   *
    * |	 |~~~|  |   The destination asserts the READY signal [...]    *
    * |	 |===|  |   and the source must keep its information stable   *
    * |	 |A  |  |   until the transfer occurs".                       *
    * |	 | X |  |   Ref: A3.2.1 Handshake process, pA3-39,            *
    *  \ |  I| /    Figure A3-2                                       *
    *   \|===|/							      *
    *    '---'							      */
   property stable_before_handshake(valid, ready, control);
      valid && !ready |-> ##1 $stable(control);
   endproperty // stable_before_handshake

   /* ,         ,                                                     *
    * |\\\\ ////| "Once VALID is asserted it must remain asserted     *
    * | \\\V/// |  until the handshake occurs, at a rising clock edge *
    * |  |~~~|  |  at which VALID and READY are both asserted".	      *
    * |  |===|  |  Ref: A3.2.1 Handshake process, pA3-39. 	      *
    * |  |A  |  |						      *
    * |  | X |  |						      *
    *  \ |  I| /						      *
    *   \|===|/							      *
    *    '---'							      */
   property valid_before_handshake(valid, ready);
      valid && !ready |-> ##1 valid;
   endproperty // valid_before_handshake

   /* ,         ,                                                     *
    * |\\\\ ////|  "The source presents the address, data or control  *
    * | \\\V/// |   information [...] and asserts the VALID signal.   *
    * |	 |~~~|	|   The destination asserts the READY signal [...]    *
    * |	 |===|	|   until the transfer occurs [...], when this        *
    * |	 |A  |	|   assertion is recognized.                          *
    * |	 | X |	|   Ref: A3.2.1 Handshake process, pA3-39,            *
    *  \ |  I| /    Figure A3-2.                                      *
    *   \|===|/							      *
    *    '---'							      */
   property valid_before_ready(valid, ready);
      valid && !ready;
   endproperty // valid_before_ready

   /* ,         ,                                                     *
    * |\\\\ ////|   "The destination asserts READY [...] indicating   *
    * | \\\V/// |    that it can accept information. The source       *
    * |	 |~~~|	|    asserts VALID after [...] In this case, transfer *
    * |	 |===|	|    occurs in a single cycle".                       *
    * |	 |A  |	|    Ref: A3.2.1 Handshake process, pA3-39            *
    * |	 | X |	|    Figure A3-3.                                     *
    *  \ |  I| /                                                      *
    *   \|===|/							      *
    *    '---'							      */
   property ready_before_valid(valid, ready);
      ready && !valid;
   endproperty // ready_before_valid

   /* ,         ,                                                     *
    * |\\\\ ////|  "Both the source and destination happen to         *
    * | \\\V/// |   indicate [...] that they can transfer the payload *
    * |	 |~~~|  |   In this case the transfer occurs at the rising    *
    * |	 |===|	|   clock edge when the assertion of both VALID and   *
    * |	 |A  |	|   READY can be recognized".                         *
    * |	 | X |	|   Ref: A3.2.1 Handshake process, pA3-40,            *
    *  \ |  I| /    Figure A3-4.                                      *
    *   \|===|/	   		                                      *
    *    '---'							      */
   property valid_with_ready(valid, ready);
      valid && ready;
   endproperty // valid_with_ready

   // Deadlock (ARM Recommended)
   /* ,         ,                                                     *
    * |\\\\ ////|  It is recommended that READY is asserted within    *
    * | \\\V/// |  MAXWAITS cycles of VALID being asserted.	      *
    * |	 |~~~|	|  This is a *potential deadlock check* that can be   *
    * |	 |===|	|  implemented as well using the strong eventually    *
    * |	 |A  |	|  operator (if the required bound is too large to be *
    * |	 | X |	|  formally efficient). Otherwise this bounded        *
    *  \ |  I| /   property works fine.                               *
    *	\|===|/							      *
    *	 '---'							      */
   property handshake_max_wait(valid, ready, timeout);
      valid & !ready |-> ##[1:timeout] ready;
   endproperty // handshake_max_wait

   property handshake_max_wait_R(valid, ready, timeout);
      (valid & !ready |-> ##[1:timeout] (!valid || ready));
   endproperty // handshake_max_wait

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *	      Section A3.2.2: Channel signaling requirements          *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */
   /* ,         ,                                                     *
    * |\\\\ ////|  "The source can assert the VALID signal only when  *
    * | \\\V/// |   it drives valid address and control information". *
    * |	 |~~~|  |   Ref: A3.2.2 Channel signaling requirements,       *
    * |	 |===|	|        pA3-40.                                      *
    * |	 |A  |	|                                                     *
    * |	 | X |	|                                                     *
    *  \ |  I| /                                                      *
    *   \|===|/	   		                                      *
    *    '---'							      */
   property valid_information(valid, sig);
      (valid |-> !$isunknown(sig));
   endproperty // valid_information

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *	            Section A3.4.1: Address structure                 *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */

   /* ,         ,                                                     *
    * |\\\\ ////|  "The start address must be aligned to the size of  *
    * | \\\V/// |   each transfer".                                   *
    * |	 |~~~|  |   Ref: A3.4.1 Address structure, pA3-48, Burst Type *
    * |	 |===|	|   WRAP.                                             *
    * |	 |A  |	|                                                     *
    * |	 | X |	|                                                     *
    *  \ |  I| /                                                      *
    *   \|===|/	   		                                      *
    *    '---'							      */
   let addr_align_check(addr, size) = (addr ==
				      (addr & (7'b1111111 << size)));
   property start_address_align(valid, burst, address, size);
      valid && (burst == amba_axi4_protocol_checker_pkg::WRAP) |->
      addr_align_check(address, size);
   endproperty // start_address_align

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *	        Section A3.4.3 Data read and write structure          *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */
   /* There is a dependency of WSTRB from this section, linked to
    * Section B1.1.3 Write strobes and Section A10.3.4 Write
    * transactions for **unused WSTRB**. I apologize in advance for
    * the mix of sections that I'm about to do, but for now I don't
    * see a need for an extra package just for this property.         */

   /* ,         ,                                                     *
    * |\\\\ ////|  "The WSTRB [...] when HIGH, specify the byte lanes *
    * | \\\V/// |   that contain valid information". A3.4.3, pA3-52.  *
    * |	 |~~~|	|   "A master must ensure that the write strobes are  *
    * |	 |===|	|    HIGH only for byte lanes that contain valid      *
    * |	 |A  |	|    data". A3.4.3, pA3-52.                           *
    * |	 | X |	|   "A master is not required to use the write strobe *
    *  \ |  I| /     signals if it always perform full data bus width *
    *   \|===|/	     transactions. The default value for wr strobes   *
    *    '---'	     is all signals asserted". A10.3.4, pA10-121.     */
   property full_data_transaction(valid, default_strb_value);
      valid |-> default_strb_value;
   endproperty // full_data_transaction

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *	     Section A3.4.4 Read and write response structure         *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */

   /* ,         ,                                                     *
    * |\\\\ ////|  "OKAY: Normal access success. Indicates that a     *
    * | \\\V/// |   normal access has been successful. Can also       *
    * |	 |~~~|	|   indicate an exclusive access has failed".         *
    * |	 |===|	|   Ref: A3.4.4 Read and write response structure,    *
    * |	 |A  |	|   pA3-57, Table A3-4.                               *
    * |	 | X |	|                                                     *
    *  \ |  I| /                                                      *
    *   \|===|/	   		                                      *
    *    '---'							      */
   property rdwr_response_okay(valid, ready, resp);
      (valid && ready &&
       (resp == amba_axi4_protocol_checker_pkg::OKAY));
   endproperty // rdwr_response_okay

   /* ,         ,                                                     *
    * |\\\\ ////|  "EXOKAY: Exclusive access okay. Indicates that     *
    * | \\\V/// |   either the read or write portion of an exclusive  *
    * |	 |~~~|	|   access has been succesful".                       *
    * |	 |===|	|   Ref: A3.4.4 Read and write response structure,    *
    * |	 |A  |	|   pA3-57, Table A3-4.                               *
    * |	 | X |	|                                                     *
    *  \ |  I| /                                                      *
    *   \|===|/	   		                                      *
    *    '---'							      */
   property rdwr_response_exokay(valid, ready, resp);
      (valid && ready &&
       (resp == amba_axi4_protocol_checker_pkg::EXOKAY));
   endproperty // rdwr_response_exokay

   /* ,         ,                                                     *
    * |\\\\ ////|  "SLVERR: Slave error. Used when the access has     *
    * | \\\V/// |   reached the slave successfully, but the slave     *
    * |	 |~~~|	|   wishes to return an error condition to the        *
    * |	 |===|	|   originating master".                              *
    * |	 |A  |	|   Ref: A3.4.4 Read and write response structure,    *
    * |	 | X |	|   pA3-57, Table A3-4.                               *
    *  \ |  I| /                                                      *
    *   \|===|/	   		                                      *
    *    '---'							      */
   property rdwr_response_slverr(valid, ready, resp);
      (valid && ready &&
       (resp == amba_axi4_protocol_checker_pkg::SLVERR));
   endproperty // rdwr_response_slverr

   /* ,         ,                                                     *
    * |\\\\ ////|  "DECERR: Decode error. Generated, typically by an  *
    * | \\\V/// |   interconnect component, to indicate that there    *
    * |	 |~~~|	|   is no slave at the transaction address.           *
    * |	 |===|	|   Ref: A3.4.4 Read and write response structure,    *
    * |	 |A  |	|   pA3-57, Table A3-4.                               *
    * |	 | X |	|                                                     *
    *  \ |  I| /                                                      *
    *   \|===|/	   		                                      *
    *    '---'							      */
   property rdwr_response_decerr(valid, ready, resp);
      (valid && ready &&
       (resp == amba_axi4_protocol_checker_pkg::DECERR));
   endproperty // rdwr_response_decerr

   // This covers are not in the spec but gives some
   // easy to get performance information
   property axi4_back_to_back(valid, ready);
      valid && ready ##1 valid;
   endproperty // axi4_back_to_back

   property axi4_wait_state(valid, ready);
      valid && !ready ##1 ready;
   endproperty // axi4_wait_state

   property axi4_no_wait_state(valid, ready);
      !valid || ready ##1 valid && ready;
   endproperty // axi4_no_wait_state

endpackage // amba_axi4_single_interface_requirements
`endif

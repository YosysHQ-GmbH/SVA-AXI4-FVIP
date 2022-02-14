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
`ifndef __AMBA_AXI4_TRANSACTION_ATTRIBUTES__
 `define __AMBA_AXI4_TRANSACTION_ATTRIBUTES__
package amba_axi4_transaction_attributes;
   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Section A4.4: Memory types                           *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */

   /* ,         ,                                                     *
    * |\\\\ ////|  "The AXI4 protocol introduces new names for the    *
    * | \\\V/// |   memory types identified by the AxCACHE encoding.  *
    * |	 |~~~|	|   Table A4-5 shows the  preferred AXI4 value with   *
    * |	 |===|	|   the legal AXI3 value in brackets.                 *
    * |	 |A  |	|   All values not shown in Table A4-5 are reserved.  *
    * |	 | X |	|   Ref: A4.4 Memory types, pA4-67, Table A4-5.       *
    *  \ |  I| /						      *
    *	\|===|/							      *
    *	 '---'							      */
   let AxCACHE_invalid_type_encoding(AxCACHE) =
       AxCACHE inside {4'h4, 4'h5, 4'h8, 4'h9, 4'hC, 4'hD};
   property memory_type_encoding(valid, cache);
      valid |-> not AxCACHE_invalid_type_encoding(cache);
   endproperty // memory_type_encoding

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Section A4.7: Access permissions                     *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */

   /* ,         ,                                                     *
    * |\\\\ ////|  "An AXI master might support more than one level   *
    * | \\\V/// |   of operating privilege, and extend this concept   *
    * |	 |~~~|	|   of privilege to memory access. AxPROT[0] identi-  *
    * |	 |===|	|   fies an access as unprivileged (0) or privile-    *
    * |	 |A  |	|   ged (1)".                                         *
    * |	 | X |	|   Ref: A4.7 Access permissions, pA4-73, Table A4-6. *
    *  \ |  I| /						      *
    *	\|===|/							      *
    *	 '---'							      */
   // The case of unprivileged access
   property unprivileged_access(valid, ready, axprot);
      valid && ready && axprot[0] == 1'b0;
   endproperty // unprivileged_access

   // The case of privileged access
   property privileged_access(valid, ready, axprot);
      valid && ready && axprot[0] == 1'b1;
   endproperty // privileged_access

   /* ,         ,                                                     *
    * |\\\\ ////|  "An AXI master might support Secure and Non-secure *
    * | \\\V/// |   operating states, and extend this concept of se-  *
    * |	 |~~~|	|   curity to memory access. AxPROT[1] identifies an  *
    * |	 |===|	|   access as Secure (0) or Non-secure (1)".          *
    * |	 |A  |	|   Ref: A4.7 Access permissions, pA4-73, Table A4-6  *
    * |	 | X |	|                                                     *
    *  \ |  I| /						      *
    *	\|===|/							      *
    *	 '---'							      */
   // The case of secure access
   property secure_access(valid, ready, axprot);
      valid && ready && axprot[1] == 1'b0;
   endproperty // secure_access

   // The case of unsecure access
   property unsecure_access(valid, ready, axprot);
      valid && ready && axprot[1] == 1'b1;
   endproperty // unsecure_access

   /* ,         ,                                                     *
    * |\\\\ ////|  "This bit indicates whether the transaction is an  *
    * | \\\V/// |   instruction access (1) or data access (0)".       *
    * |	 |~~~|	|   Note: The AXI protocol defines this indication as *
    * |	 |===|	|   a hint. It is not accurate in all cases.          *
    * |	 |A  |	|   Ref: A4.7 Access permissions, pA4-73, Table A4-6  *
    * |	 | X |	|                                                     *
    *  \ |  I| /						      *
    *	\|===|/							      *
    *	 '---'							      */
   // The case of data access
   property data_access(valid, ready, axprot);
      valid && ready && axprot[2] == 1'b0;
   endproperty // data_access

   // The case of instruction access
   property instruction_access(valid, ready, axprot);
      valid && ready && axprot[2] == 1'b1;
   endproperty // instruction_access
endpackage // amba_axi4_transaction_attributes
`endif

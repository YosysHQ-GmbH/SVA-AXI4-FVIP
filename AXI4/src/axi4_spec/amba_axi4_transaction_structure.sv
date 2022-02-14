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
`ifndef __AMBA_AXI4_TRANSACTION_STRUCTURE__
 `define __AMBA_AXI4_TRANSACTION_STRUCTURE__
package amba_axi4_transaction_structure;
   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		   Section A3.4.1 Address structure                   *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */

   /* ,         ,                                                     *
    * |\\\\ ////|  "AXI4 extends burst length support for the INCR    *
    * | \\\V/// |   burst type to 1 to 256 transfers. Support for all *
    * |	 |~~~|	|   other burst types in AXI4 remains at 1 to 16      *
    * |	 |===|	|   transfers".                                       *
    * |	 |A  |	|   Ref: A3.4.1 Address structure, pA3-46.            *
    * |	 | X |	|                                                     *
    *  \ |  I| /	                                              *
    *	\|===|/							      *
    *	 '---'							      */
   property supported_burst_transfer(valid, burst, burst_type, len_val);
      (valid && burst == burst_type |-> len_val);
   endproperty // supported_burst_transfer

   /* ,         ,                                                     *
    * |\\\\ ////|  "AXI has the following rules governing the use of  *
    * | \\\V/// |   bursts:                                           *
    * |	 |~~~|	|     * for wrapping bursts, the burst length must be *
    * |	 |===|	|       2, 4, 8 or 16 [...]".                         *
    * |	 |A  |	|   Ref: A3.4.1 Address structure, pA3-46.            *
    * |	 | X |	|                                                     *
    *  \ |  I| /	                                              *
    *	\|===|/							      *
    *	 '---'							      */
   property valid_wrap_burst_length(valid, burst, len);
      (valid && burst == amba_axi4_protocol_checker_pkg::WRAP |->
       len inside {8'd1, 8'd3, 8'd7, 8'd15});
   endproperty // valid_wrap_burst_length

   /* ,         ,                                                     *
    * |\\\\ ////|  "AXI has the following rules governing the use of  *
    * | \\\V/// |   bursts:                                           *
    * |	 |~~~|	|     * a burst must not cross a 4KB address          *
    * |	 |===|	|       boundary".                                    *
    * |	 |A  |	|   Ref: A3.4.1 Address structure, pA3-46.            *
    * |	 | X |	|                                                     *
    *  \ |  I| /	                                              *
    *	\|===|/							      *
    *	 '---'							      */
   property burst_cache_line_boundary(valid, burst, cond);
      (valid && burst == amba_axi4_protocol_checker_pkg::INCR |-> cond);
   endproperty // burst_cache_line_boundary

   /* ,         ,                                                     *
    * |\\\\ ////|  "The size of any transfer must not exceed the data *
    * | \\\V/// |   bus width of either agent in the transaction".    *
    * |	 |~~~|	|                                                     *
    * |	 |===|	|   Ref: A3.4.1 Address structure, Burst size,        *
    * |	 |A  |	|   pA3-47.                                           *
    * |	 | X |	|                                                     *
    *  \ |  I| /	                                              *
    *	\|===|/							      *
    *	 '---'							      */
   let calc_max_size(w) = $clog2(w);
   property burst_size_within_width_boundary(valid, size, strb);
      (valid |-> size <= calc_max_size(strb));
   endproperty // burst_size_within_width_boundary
endpackage
`endif

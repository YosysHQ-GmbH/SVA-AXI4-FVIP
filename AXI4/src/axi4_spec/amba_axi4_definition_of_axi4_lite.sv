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
`ifndef __AMBA_AXI4_DEFINITION_OF_AXI4_LITE__
 `define __AMBA_AXI4_DEFINITION_OF_AXI4_LITE__
package amba_axi4_definition_of_axi4_lite;
   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Section B1.1: Definition of AXI4-Lite                *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */

   /* ,         ,                                                     *
    * |\\\\ ////|  "All data accesses use the full width of the data  *
    * | \\\V/// |   bus.                                              *
    * |	 |~~~|	|   AXI4-Lite supports a data bus width of 32-bit     *
    * |	 |===|	|   or 64-bit".                                       *
    * |	 |A  |	|   Ref: B1.1 Definition of AXI4-Lite, pB1-126        *
    * |	 | X |	|						      *
    *  \ |  I| /						      *
    *	\|===|/							      *
    *	 '---'							      */
   property axi4l_databus_width(data_width);
      data_width inside {32, 64};
   endproperty // axi4l_databus_width

   /* ,         ,                                                     *
    * |\\\\ ////|  "Exclusive accesses are not supported".            *
    * | \\\V/// |   Ref: B1.1 Definition of AXI4-Lite, pB1-126.       *
    * |	 |~~~|	|                                                     *
    * |	 |===|	|                                                     *
    * |	 |A  |	|                                                     *
    * |	 | X |	|						      *
    *  \ |  I| /						      *
    *	\|===|/							      *
    *	 '---'							      */
   property unsupported_exclusive_access(valid, lock, value);
      valid |-> lock != value;
   endproperty // unsupported_exclusive_access

   /* ,         ,                                                     *
    * |\\\\ ////|  "The EXOKAY response is not supported on the read  *
    * | \\\V/// |   data and write response channels".                *
    * |	 |~~~|	|   Ref: B1.1.1 Signal List, pB1-126.                 *
    * |	 |===|	|                                                     *
    * |	 |A  |	|                                                     *
    * |	 | X |	|						      *
    *  \ |  I| /						      *
    *	\|===|/							      *
    *	 '---'							      */
   property unsupported_transfer_status(valid, response, value);
      valid |-> response != value;
   endproperty // unsupported_transfer_status

   /* ,         ,                                                     *
    * |\\\\ ////|  "Table B1-1 shows the required signals on an       *
    * | \\\V/// |   AXI4-Lite interface".                             *
    * |	 |~~~|	|   Ref: B1.1.1 Signal List, pB1-126.                 *
    * |	 |===|	|   Including:                                        *
    * |	 |A  |	|   AXI4 signals modified in AXI4-Lite,               *
    * |	 | X |	|   AXI4 signals not supported in AXI4-Lite           *
    *  \ |  I| /    B1.1.2 Bus width,				      *
    *	\|===|/	    B1.1.3 Write strobes,    		              *
    *	 '---'      B1.1.4 Optional signaling.			      */
   property axi4_lite_unsupported_sig(axi4_lite_sig_bundle);
      axi4_lite_sig_bundle;
   endproperty // axi4_lite_unsupported_sig
endpackage // amba_axi4_definition_of_axi4_lite
`endif //  `ifndef __AMBA_AXI4_DEFINITION_OF_AXI4_LITE__

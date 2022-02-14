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
`default_nettype none
module amba_axi4_exclusive_access_source_perspective
  import amba_axi4_protocol_checker_pkg::*;
   #(parameter axi4_checker_params_t cfg =
     '{ID_WIDTH:          4,
       VERIFY_AGENT_TYPE: SOURCE,
       PROTOCOL_TYPE:     AXI4LITE,
       default: '0})
   (input wire ACLK, ARESETn,
    input wire [cfg.ID_WIDTH-1:0] ARID, AWID,
    input wire ARVALID, ARLOCK,
    input wire AWVALID, AWLOCK);

   default clocking fpv_clk @(posedge ACLK); endclocking
   default disable iff(!ARESETn);

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Section A7.2 Exclusive accesses                      *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */

   /* ,         ,                                                     *
    * |\\\\ ////|  "A master must not start the write part of an      *
    * | \\\V/// |   exclusive access sequence until the read part is  *
    * |	 |~~~|	|   complete".                                        *
    * |	 |===|	|   Ref: A7.2.2 Exclusive access from the perspective *
    * |	 |A  |	|        of the master, pA7-96.                       *
    * |	 | X |	|                                                     *
    *  \ |  I| /	                                              *
    *	\|===|/							      *
    *	 '---'							      */
   /* This is an important property for crossbars as far as I'm
    * concerned. What I don't understand is why AMBA DUI0534 formalises
    * this property somehow complex. I am missing something?.
    * Allow me to explain: if a system should not start AW in
    * EXCLUSIVE with R in EXCLUSIVE, it is not sufficient to check
    * that these two conditions never happens at the same time? ...
    * We'll figure it out in the next test of `amba_validity_test`. */
   sequence exclusive_write_read(avalid, aid, alock, arvalid, arid, arlock);
      aid == arid          ##0
      avalid               ##0
      arvalid              ##0
      alock  ==  EXCLUSIVE ##0
      arlock == EXCLUSIVE;
   endsequence // exclusive_write_read

   property exclusive_wr_rd_simultaneously;
      (not (exclusive_write_read(AWVALID, AWID, AWLOCK, ARVALID, ARID, ARLOCK)));
   endproperty

   generate
      if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	 ap_NO_WR_RD_EXCLUSIVE_simultaneously: assert property(exclusive_wr_rd_simultaneously)
	   else $error("Violation: A master must not start the write part of an exclusive",
		       "access sequence until the read part is complete.",
		       "(A7.2.2 Exclusive access from the perspective of the master, pA7-96).");
      end
      else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
	 cp_NO_WR_RD_EXCLUSIVE_simultaneously: assume property(exclusive_wr_rd_simultaneously)
	   else $error("Violation: A master must not start the write part of an exclusive",
		       "access sequence until the read part is complete.",
		       "(A7.2.2 Exclusive access from the perspective of the master, pA7-96).");
      end
   endgenerate
endmodule // amba_axi4_exclusive_access_source_perspective
`default_nettype wire

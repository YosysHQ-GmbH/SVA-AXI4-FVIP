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
 */
`default_nettype none
module amba_axi4_protocol_checker
  import amba_axi4_protocol_checker_pkg::*;
   #(parameter axi4_checker_params_t cfg =
     '{ID_WIDTH:          4,
       ADDRESS_WIDTH:     32,
       DATA_WIDTH:        64,
       AWUSER_WIDTH:      32,
       WUSER_WIDTH:       32,
       BUSER_WIDTH:       32,
       ARUSER_WIDTH:      32,
       RUSER_WIDTH:       32,
       MAX_WR_BURSTS:     4,
       MAX_RD_BURSTS:     4,
       MAX_WR_LENGTH:     8,
       MAX_RD_LENGTH:     8,
       MAXWAIT:           16,
       VERIFY_AGENT_TYPE: SOURCE,
       PROTOCOL_TYPE:     AXI4LITE,
       ENABLE_COVER:      1,
       ENABLE_XPROP:      1,
       ARM_RECOMMENDED:   1,
       CHECK_PARAMETERS:  1,
       OPTIONAL_WSTRB:    1,
       FULL_WR_STRB:      1,
       OPTIONAL_RESET:    1,
       EXCLUSIVE_ACCESS:  1},
     // Read only
     localparam unsigned STRB_WIDTH = cfg.DATA_WIDTH/8)
   (input wire                         ACLK,
    input wire 			       ARESETn,
    // Write Address Channel (AW)
    input wire [cfg.ID_WIDTH-1:0]      AWID,
    input wire [cfg.ADDRESS_WIDTH-1:0] AWADDR,
    input wire [7:0] 		       AWLEN,
    input wire [2:0] 		       AWSIZE,
    input wire [1:0] 		       AWBURST,
    input wire 			       AWLOCK,
    input wire [3:0] 		       AWCACHE,
    input wire [2:0] 		       AWPROT,
    input wire [3:0] 		       AWQOS,
    input wire [3:0] 		       AWREGION,
    input wire [cfg.AWUSER_WIDTH-1:0]  AWUSER,
    input wire 			       AWVALID,
    input wire 			       AWREADY,
    // Write Data Channel (W)
    input wire [cfg.DATA_WIDTH-1:0]    WDATA,
    input wire [STRB_WIDTH-1:0]        WSTRB,
    input wire 			       WLAST,
    input wire [cfg.WUSER_WIDTH-1:0]   WUSER,
    input wire 			       WVALID,
    input wire 			       WREADY,
    // Write Response Channel (B)
    input wire [cfg.ID_WIDTH-1:0]      BID,
    input wire [1:0] 		       BRESP,
    input wire [cfg.BUSER_WIDTH-1:0]   BUSER,
    input wire 			       BVALID,
    input wire 			       BREADY,
    // Read Address Channel (AR)
    input wire [cfg.ID_WIDTH-1:0]      ARID,
    input wire [cfg.ADDRESS_WIDTH-1:0] ARADDR,
    input wire [7:0] 		       ARLEN,
    input wire [2:0] 		       ARSIZE,
    input wire [1:0] 		       ARBURST,
    input wire 			       ARLOCK,
    input wire [3:0] 		       ARCACHE,
    input wire [2:0] 		       ARPROT,
    input wire [3:0] 		       ARQOS,
    input wire [3:0] 		       ARREGION,
    input wire [cfg.ARUSER_WIDTH-1:0]  ARUSER,
    input wire 			       ARVALID,
    input wire 			       ARREADY,
    // Read Data Channel (R)
    input wire [cfg.ID_WIDTH-1:0]      RID,
    input wire [cfg.DATA_WIDTH-1:0]    RDATA,
    input wire [1:0] 		       RRESP,
    input wire 			       RLAST,
    input wire [cfg.RUSER_WIDTH-1:0]   RUSER,
    input wire 			       RVALID,
    input wire 			       RREADY);

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Section A1.3: AXI Architecture                       *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */

   /* ,         ,                                                     *
    * |\\\\ ////|  "The AXI protocol is burst-based and defines the   *
    * | \\\V/// |   following ~independent~ transaction channels:  "  *
    * |	 |~~~|	|   Ref: A1.3 AXI Architecture, pA1-24.               *
    * |	 |===|	|                                                     *
    * |	 |A  |	|                                                     *
    * |	 | X |	|						      *
    *  \ |  I| /						      *
    *	\|===|/							      *
    *	 '---'							      */
   /* The amba_axi4_protocol_checker is composed of five checkers,
    * each checker models assertions for the five transaction
    * channels defined in 'A1.3 AXI Architecture'.
    * These checkers are independent of each other as well, honoring
    * the architectural obligation from the AXI spec.
    * In other words, the user can bind this module to excercise the
    * AXI channels at once, or take any of the modules instantiated
    * here to verify a channel in particular. */

   // Write addres channel properties
   amba_axi4_write_address_channel
     #(.cfg(cfg)) AW_channel_checker(.*);

   // Write data channel properties
   amba_axi4_write_data_channel
     #(.cfg(cfg)) W_channel_checker(.*);

   // Write response channel properties
   amba_axi4_write_response_channel
     #(.cfg(cfg)) B_channel_checker(.*);

   // Read address channel properties
   amba_axi4_read_address_channel
     #(.cfg(cfg)) AR_channel_checker(.*);

   // Read data channel properties
   amba_axi4_read_data_channel
     #(.cfg(cfg)) R_channel_checker(.*);

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                    Under heavy development                      *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   amba_axi4_write_response_dependencies
     #(.cfg(cfg)) yosyshq_amba4_abstract_checker(.*);

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
   amba_axi4_exclusive_access_source_perspective
     #(.cfg(cfg)) yosyshq_amba4_exclusive_abstract_checker(.*);
endmodule // amba_axi4_protocol_checker
`default_nettype wire

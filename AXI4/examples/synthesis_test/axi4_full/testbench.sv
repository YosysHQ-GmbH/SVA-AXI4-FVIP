`default_nettype none
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
import amba_axi4_protocol_checker_pkg::*;
// Connect a constraint entity
localparam axi4_checker_params_t
  cfg_cons =
	    '{ID_WIDTH:          4,
	      ADDRESS_WIDTH:     32,
	      DATA_WIDTH:        64,
	      AWUSER_WIDTH:      32,
	      WUSER_WIDTH:       32,
	      BUSER_WIDTH:       32,
	      ARUSER_WIDTH:      32,
	      RUSER_WIDTH:       32,
	      MAX_WR_BURSTS:     16,
	      MAX_RD_BURSTS:     16,
	      MAX_WR_LENGTH:     8,
	      MAX_RD_LENGTH:     8,
	      MAXWAIT:           16,
	      VERIFY_AGENT_TYPE: CONSTRAINT,
	      PROTOCOL_TYPE:     AXI4FULL,
	      INTERFACE_REQS:    1,
	      ENABLE_COVER:      1,
	      ENABLE_XPROP:      1,
	      ARM_RECOMMENDED:   1,
	      CHECK_PARAMETERS:  1,
	      OPTIONAL_WSTRB:    1,
	      FULL_WR_STRB:      1,
	      OPTIONAL_RESET:    1,
	      EXCLUSIVE_ACCESS:  1};
bind testbench amba_axi4_protocol_checker #(.cfg(cfg_cons)) assumes_provider (.*);

// Connect a monitor entity
localparam axi4_checker_params_t
  cfg_mon =
	   '{ID_WIDTH:          4,
	     ADDRESS_WIDTH:     32,
	     DATA_WIDTH:        64,
	     AWUSER_WIDTH:      32,
	     WUSER_WIDTH:       32,
	     BUSER_WIDTH:       32,
	     ARUSER_WIDTH:      32,
	     RUSER_WIDTH:       32,
	     MAX_WR_BURSTS:     16,
	     MAX_RD_BURSTS:     16,
	     MAX_WR_LENGTH:     8,
	     MAX_RD_LENGTH:     8,
	     MAXWAIT:           16,
	     VERIFY_AGENT_TYPE: MONITOR,
	     PROTOCOL_TYPE:     AXI4FULL,
	     ENABLE_COVER:      1,
	     INTERFACE_REQS:    1,
	     ENABLE_XPROP:      1,
	     ARM_RECOMMENDED:   1,
	     CHECK_PARAMETERS:  1,
	     OPTIONAL_WSTRB:    1,
	     FULL_WR_STRB:      1,
	     OPTIONAL_RESET:    1,
	     EXCLUSIVE_ACCESS:  1};
bind testbench amba_axi4_protocol_checker #(.cfg(cfg_mon)) asserts_provider (.*);

// The actual interface
module testbench
  #(parameter axi4_checker_params_t cfg =
    '{ID_WIDTH:          4,
      ADDRESS_WIDTH:     32,
      DATA_WIDTH:        64,
      AWUSER_WIDTH:      32,
      WUSER_WIDTH:       32,
      BUSER_WIDTH:       32,
      ARUSER_WIDTH:      32,
      RUSER_WIDTH:       32,
      MAX_WR_BURSTS:     16,
      MAX_RD_BURSTS:     16,
      MAX_WR_LENGTH:     8,
      MAX_RD_LENGTH:     8,
      MAXWAIT:           16,
      VERIFY_AGENT_TYPE: SOURCE,
      PROTOCOL_TYPE:     AXI4FULL,
      INTERFACE_REQS:    1,
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
    *		        Back to back connection                       *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */
endmodule // amba_axi4_protocol_checker
`default_nettype wire

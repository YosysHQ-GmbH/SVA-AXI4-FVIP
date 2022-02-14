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

// Bind the YosysHQ IP to the DUT
bind <dut> amba_axi4_protocol_checker
  // But first define the configuration of the YosysHQ SVA Formal IP
  #(.cfg('{ID_WIDTH:          4,
	   ADDRESS_WIDTH:     32,
	   DATA_WIDTH:        32,
	   AWUSER_WIDTH:      32,
	   WUSER_WIDTH:       32,
	   BUSER_WIDTH:       32,
	   ARUSER_WIDTH:      32,
	   RUSER_WIDTH:       32,
	   MAXWAIT:           16,
	   VERIFY_AGENT_TYPE: amba_axi4_protocol_checker_pkg::SOURCE,
	   PROTOCOL_TYPE:     amba_axi4_protocol_checker_pkg::AXI4FULL,
	   ENABLE_COVER:      1,
	   ARM_RECOMMENDED:   1,
	   CHECK_PARAMETERS:  1,
	   OPTIONAL_WSTRB:    1,
	   FULL_WR_STRB:      1,
	   OPTIONAL_RESET:    1,
	   EXCLUSIVE_ACCESS:  1})) yosyshq_axi4_full_checker_source
    (.ACLK(),
     .ARESETn(),
     // Write Address Channel (AW)
     .AWID(),
     .AWADDR(),
     .AWLEN(),
     .AWSIZE(),
     .AWBURST(),
     .AWLOCK(),
     .AWCACHE(),
     .AWPROT(),
     .AWQOS(),
     .AWREGION(),
     .AWUSER(),
     .AWVALID(),
     .AWREADY(),
     // Write Data Channel (W)
     .WDATA(),
     .WSTRB(),
     .WLAST(),
     .WUSER(),
     .WVALID(),
     .WREADY(),
     // Write Response Channel (B)
     .BID(),
     .BRESP(),
     .BUSER(),
     .BVALID(),
     .BREADY(),
     // Read Address Channel (AR)
     .ARID(),
     .ARADDR(),
     .ARLEN(),
     .ARSIZE(),
     .ARBURST(),
     .ARLOCK(),
     .ARCACHE(),
     .ARPROT(),
     .ARQOS(),
     .ARREGION(),
     .ARUSER(),
     .ARVALID(),
     .ARREADY(),
     // Read Data Channel (R)
     .RID(),
     .RDATA(),
     .RRESP(),
     .RLAST(),
     .RUSER(),
     .RVALID(),
     .RREADY());
`default_nettype wire

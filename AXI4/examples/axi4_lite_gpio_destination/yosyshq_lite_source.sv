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
//`default_nettype none

// Bind the YosysHQ IP to the DUT
bind axilgpio amba_axi4_protocol_checker
  // But first define the configuration of the YosysHQ SVA Formal IP
  #(.cfg('{ID_WIDTH:          4,
	   ADDRESS_WIDTH:     32,
	   DATA_WIDTH:        32,
	   AWUSER_WIDTH:      32,
	   WUSER_WIDTH:       32,
	   BUSER_WIDTH:       32,
	   ARUSER_WIDTH:      32,
	   RUSER_WIDTH:       32,
	   MAX_WR_BURSTS:     1,
	   MAX_RD_BURSTS:     1,
	   MAX_WR_LENGTH:     1,
	   MAX_RD_LENGTH:     1,
	   MAXWAIT:           16,
	   VERIFY_AGENT_TYPE: amba_axi4_protocol_checker_pkg::DESTINATION,
	   PROTOCOL_TYPE:     amba_axi4_protocol_checker_pkg::AXI4LITE,
	   ENABLE_COVER:      1,
	   ENABLE_XPROP:      0,
	   ARM_RECOMMENDED:   1,
	   CHECK_PARAMETERS:  1,
	   OPTIONAL_WSTRB:    1,
	   FULL_WR_STRB:      1,
	   OPTIONAL_RESET:    0,
	   EXCLUSIVE_ACCESS:  1})) yosyshq_axi4_checker_destination
  (.ACLK(S_AXI_ACLK),
   .ARESETn(S_AXI_ARESETN),

   .AWVALID(S_AXI_AWVALID),
   .AWREADY(S_AXI_AWREADY),
   .AWADDR(S_AXI_AWADDR),
   .AWPROT(S_AXI_AWPROT),

   .WVALID(S_AXI_WVALID),
   .WREADY(S_AXI_WREADY),
   .WDATA(S_AXI_WDATA),
   .WSTRB(S_AXI_WSTRB),

   .BVALID(S_AXI_BVALID),
   .BREADY(S_AXI_BREADY),
   .BRESP(S_AXI_BRESP),

   .ARVALID(S_AXI_ARVALID),
   .ARREADY(S_AXI_ARREADY),
   .ARADDR(S_AXI_ARADDR),
   .ARPROT(S_AXI_ARPROT),

   .RVALID(S_AXI_RVALID),
   .RREADY(S_AXI_RREADY),
   .RDATA(S_AXI_RDATA),
   .RRESP(S_AXI_RRESP));
`default_nettype wire

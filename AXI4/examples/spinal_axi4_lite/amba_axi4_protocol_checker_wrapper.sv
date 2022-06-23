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
bind AxiLite4FormalComponent amba_axi4_protocol_checker
  #('{ID_WIDTH:          4,
      ADDRESS_WIDTH:     32,
      DATA_WIDTH:        32,
      AWUSER_WIDTH:      1,
      WUSER_WIDTH:       1,
      BUSER_WIDTH:       1,
      ARUSER_WIDTH:      1,
      RUSER_WIDTH:       1,
      MAX_WR_BURSTS:     2,
      MAX_RD_BURSTS:     2,
      MAX_WR_LENGTH:     4,
      MAX_RD_LENGTH:     4,
      MAXWAIT:           16,
      VERIFY_AGENT_TYPE: amba_axi4_protocol_checker_pkg::SOURCE,
      PROTOCOL_TYPE:     amba_axi4_protocol_checker_pkg::AXI4LITE,
      INTERFACE_REQS:    1,
      ENABLE_COVER:      1,
      ENABLE_XPROP:      1,
      ARM_RECOMMENDED:   1,
      CHECK_PARAMETERS:  1,
      OPTIONAL_WSTRB:    0,
      FULL_WR_STRB:      0,
      OPTIONAL_RESET:    0,
      EXCLUSIVE_ACCESS:  1,
      OPTIONAL_LP:       0})
spinal_test (.ACLK(clk),
	     .ARESETn(reset),

	     .AWVALID(io_bus_aw_valid),
	     .AWREADY(io_bus_aw_ready),
	     .AWADDR(io_bus_aw_payload_addr),
	     .AWPROT(io_bus_aw_payload_prot),

	     .WVALID(io_bus_w_valid),
	     .WREADY(io_bus_w_ready),
	     .WDATA(io_bus_w_payload_data),
	     .WSTRB(io_bus_w_payload_strb),

	     .BVALID(io_bus_b_valid),
	     .BREADY(io_bus_b_ready),
	     .BRESP(io_bus_b_payload_resp),

	     .ARVALID(io_bus_ar_valid),
	     .ARREADY(io_bus_ar_ready),
	     .ARADDR(io_bus_ar_payload_addr),
	     .ARPROT(io_bus_ar_payload_prot),

	     .RVALID(io_bus_r_valid),
	     .RREADY(io_bus_r_ready),
	     .RDATA(io_bus_r_payload_data),
	     .RRESP(io_bus_r_payload_resp));
`default_nettype wire

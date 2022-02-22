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
bind axi_crossbar amba_axi4_protocol_checker
  #('{ID_WIDTH:          4,
      ADDRESS_WIDTH:     32,
      DATA_WIDTH:        32,
      AWUSER_WIDTH:      1,
      WUSER_WIDTH:       1,
      BUSER_WIDTH:       1,
      ARUSER_WIDTH:      1,
      RUSER_WIDTH:       1,
      MAX_WR_BURSTS:     1,
      MAX_RD_BURSTS:     1,
      MAX_WR_LENGTH:     1,
      MAX_RD_LENGTH:     1,
      MAXWAIT:           20,
      VERIFY_AGENT_TYPE: amba_axi4_protocol_checker_pkg::SOURCE,
      PROTOCOL_TYPE:     amba_axi4_protocol_checker_pkg::AXI4FULL,
      INTERFACE_REQS:    1,
      ENABLE_COVER:      1,
      ENABLE_XPROP:      0,
      ARM_RECOMMENDED:   1,
      CHECK_PARAMETERS:  1,
      OPTIONAL_WSTRB:    1,
      FULL_WR_STRB:      1,
      OPTIONAL_RESET:    0,
      EXCLUSIVE_ACCESS:  1,
      OPTIONAL_LP:       0})
source_chk (
	    .ACLK(clk),
	    .ARESETn(!rst),

	    .AWID(m_axi_awid),
	    .AWADDR(m_axi_awaddr),
	    .AWREGION(m_axi_awregion),
	    .AWLEN(m_axi_awlen),
	    .AWSIZE(m_axi_awsize),
	    .AWBURST(m_axi_awburst),
	    .AWLOCK(m_axi_awlock),
	    .AWCACHE(m_axi_awcache),
	    .AWPROT(m_axi_awprot),
	    .AWQOS(m_axi_awqos),
	    .AWVALID(m_axi_awvalid),
	    .AWREADY(m_axi_awready),
	    .AWUSER(m_axi_awuser),

	    .WDATA(m_axi_wdata),
	    .WSTRB(m_axi_wstrb),
	    .WLAST(m_axi_wlast),
	    .WVALID(m_axi_wvalid),
	    .WREADY(m_axi_wready),
	    .WUSER(m_axi_wuser),

	    .BID(m_axi_bid),
	    .BRESP(m_axi_bresp),
	    .BVALID(m_axi_bvalid),
	    .BREADY(m_axi_bready),
	    .BUSER(m_axi_buser),

	    .ARID(m_axi_arid),
	    .ARADDR(m_axi_araddr),
	    .ARREGION(m_axi_arregion),
	    .ARLEN(m_axi_arlen),
	    .ARSIZE(m_axi_arsize),
	    .ARBURST(m_axi_arburst),
	    .ARLOCK(m_axi_arlock),
	    .ARCACHE(m_axi_arcache),
	    .ARPROT(m_axi_arprot),
	    .ARQOS(m_axi_arqos),
	    .ARVALID(m_axi_arvalid),
	    .ARREADY(m_axi_arready),
	    .ARUSER(m_axi_aruser),

	    .RID(m_axi_rid),
	    .RDATA(m_axi_rdata),
	    .RRESP(m_axi_rresp),
	    .RLAST(m_axi_rlast),
	    .RVALID(m_axi_rvalid),
	    .RREADY(m_axi_rready),
	    .RUSER(m_axi_ruser)
	    );

// Connect a destination entity
bind axi_crossbar amba_axi4_protocol_checker
  #('{ID_WIDTH:          4,
      ADDRESS_WIDTH:     32,
      DATA_WIDTH:        32,
      AWUSER_WIDTH:      1,
      WUSER_WIDTH:       1,
      BUSER_WIDTH:       1,
      ARUSER_WIDTH:      1,
      RUSER_WIDTH:       1,
      MAX_WR_BURSTS:     1,
      MAX_RD_BURSTS:     1,
      MAX_WR_LENGTH:     1,
      MAX_RD_LENGTH:     1,
      MAXWAIT:           20,
      VERIFY_AGENT_TYPE: amba_axi4_protocol_checker_pkg::DESTINATION,
      PROTOCOL_TYPE:     amba_axi4_protocol_checker_pkg::AXI4FULL,
      INTERFACE_REQS:    1,
      ENABLE_COVER:      1,
      ENABLE_XPROP:      0,
      ARM_RECOMMENDED:   0,
      CHECK_PARAMETERS:  1,
      OPTIONAL_WSTRB:    1,
      FULL_WR_STRB:      1,
      OPTIONAL_RESET:    0,
      EXCLUSIVE_ACCESS:  1,
      OPTIONAL_LP:       0})
dest_check (
	    .ACLK(clk),
	    .ARESETn(!rst),

	    .AWID(s_axi_awid),
	    .AWADDR(s_axi_awaddr),
	    .AWREGION(4'h0),
	    .AWLEN(s_axi_awlen),
	    .AWSIZE(s_axi_awsize),
	    .AWBURST(s_axi_awburst),
	    .AWLOCK(s_axi_awlock),
	    .AWCACHE(s_axi_awcache),
	    .AWPROT(s_axi_awprot),
	    .AWQOS(s_axi_awqos),
	    .AWVALID(s_axi_awvalid),
	    .AWREADY(s_axi_awready),
	    .AWUSER(s_axi_awuser),

	    .WDATA(s_axi_wdata),
	    .WSTRB(s_axi_wstrb),
	    .WLAST(s_axi_wlast),
	    .WVALID(s_axi_wvalid),
	    .WREADY(s_axi_wready),
	    .WUSER(s_axi_wuser),

	    .BID(s_axi_bid),
	    .BRESP(s_axi_bresp),
	    .BVALID(s_axi_bvalid),
	    .BREADY(s_axi_bready),
	    .BUSER(s_axi_buser),

	    .ARID(s_axi_arid),
	    .ARADDR(s_axi_araddr),
	    .ARREGION(4'h0),
	    .ARLEN(s_axi_arlen),
	    .ARSIZE(s_axi_arsize),
	    .ARBURST(s_axi_arburst),
	    .ARLOCK(s_axi_arlock),
	    .ARCACHE(s_axi_arcache),
	    .ARPROT(s_axi_arprot),
	    .ARQOS(s_axi_arqos),
	    .ARVALID(s_axi_arvalid),
	    .ARREADY(s_axi_arready),
	    .ARUSER(s_axi_aruser),

	    .RID(s_axi_rid),
	    .RDATA(s_axi_rdata),
	    .RRESP(s_axi_rresp),
	    .RLAST(s_axi_rlast),
	    .RVALID(s_axi_rvalid),
	    .RREADY(s_axi_rready),
	    .RUSER(s_axi_ruser)
	    );
`default_nettype wire

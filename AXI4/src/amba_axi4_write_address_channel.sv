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
module amba_axi4_write_address_channel
  import amba_axi4_protocol_checker_pkg::*;
   #(parameter axi4_checker_params_t cfg =
     '{ID_WIDTH:          4,
       ADDRESS_WIDTH:     32,
       DATA_WIDTH:        32,
       AWUSER_WIDTH:      32,
       MAX_WR_BURSTS:     2,
       MAX_WR_LENGTH:     8,
       VERIFY_AGENT_TYPE: SOURCE,
       PROTOCOL_TYPE:     AXI4LITE,
       CHECK_PARAMETERS:  1,
       INTERFACE_REQS:    1,
       ENABLE_COVER:      1,
       ENABLE_XPROP:      1,
       ARM_RECOMMENDED:   1,
       MAXWAIT:           16,
       OPTIONAL_RESET:    1,
       EXCLUSIVE_ACCESS:  1,
       default:           0},
     // Read only
     localparam unsigned STRB_WIDTH = cfg.DATA_WIDTH/8,
     localparam unsigned BURST_SIZE_MAX = $clog2(STRB_WIDTH),
     localparam unsigned WRITE_BURST_MAX = 256)
   (input wire                         ACLK,
    input wire 			       ARESETn,
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
    input wire 			       AWREADY);

   // Import the properties in this scope
   import amba_axi4_definition_of_axi4_lite::*;
   import amba_axi4_single_interface_requirements::*;
   import amba_axi4_transaction_structure::*;
   import amba_axi4_transaction_attributes::*;
   import amba_axi4_atomic_accesses::*;

   // Default clocking for all properties
   default clocking axi4_aclk @(posedge ACLK); endclocking

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		               Helper logic                           *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */

   // Configure unsupported AXI4-Lite signals
   bit AW_unsupported_sig;
   // "all transactions are of burst length 1".
   // "all data accesses use the full width of the data bus".
   // "AXI4-Lite supports a data bus width of 32-bit or 64-bit". (B1.1, pB1-126).
   // AXI4-Lite can have a burst size of either 4 (AWSIZE=3'b010) or 8 (AWSIZE=3'b011).
   // which is log2(STRB_WIDTH) [if WDATA = 32, STRB=32/8=4, log2(4)=2=AWSIZE of 3'b010.
   localparam MAX_SIZE = $clog2(STRB_WIDTH);
   assign AW_unsupported_sig = (/* The burst length is defined to be 1,
                                 * equivalent to an AxLEN value of zero. */
                                AWLEN    == 8'b00000000 &&
                                /* All accesses are defined to be the width
                                 * of the data bus. */
                                AWSIZE   == MAX_SIZE &&
                                /* The burst type has no meaning because the burst
                                 * length is 1. */
                                AWBURST  == 2'b00 &&
                                /* All accesses are defined as Normal accesses,
                                 * equivalent to an AxLOCK value of zero. */
                                AWLOCK   == 1'b0 &&
                                /* All accesses are defined as Non-modifiable,
                                 * Non-bufferable, equivalent to an AxCACHE
                                 * value of 0b0000. */
                                AWCACHE  == 4'b0000 &&
                                /* A default value of 0b0000 indicates that
                                 * the interface is not participating in any
                                 * QoS scheme. */
                                AWQOS    == 4'b0000 &&
                                /* Table A10-1 Master interface write channel
                                 * signals and default signal values.
                                 * AWREGION Default all zeros. */
                                AWREGION == 4'b0000 &&
                                /* Optional User-defined signal in the write address channel.
                                 * Supported only in AXI4. */
                                AWUSER   == {cfg.AWUSER_WIDTH{1'b0}} &&
                                /* AXI4-Lite does not support AXI IDs. This means
                                 * all transactions must be in order, and all
                                 * accesses use a single fixed ID value. */
                                AWID     == {cfg.ID_WIDTH{1'b0}});

   /* Upper 4 bits are never set for AxLEN <= 16.
    * it can also be: let FIXED_len = AWLEN inside {[0:15]} */
   let AW_FIXED_len = AWLEN[7:4] == 4'b000;

   logic [cfg.ADDRESS_WIDTH-1:0] end_addr;
   logic aw_4KB_boundary;
   generate
      if(cfg.PROTOCOL_TYPE == AXI4FULL && cfg.ADDRESS_WIDTH > 12) begin
	 /* The calculation of the end address of an incremental burst depends on AxSIZE,
	  * AxADDR and AxLEN as follows:
	  * end_address = AxADDR[ADDR_WIDTH-1:AxSIZE] + {AxLEN, AxSIZE}, for each AxSIZE.
	  * The concatenation between AxLEN and AxSIZE can be represented with a shift
	  * operation: AxLEN << AxSIZE. This simplifies the logic a bit (instead of
	  * creating: case(AxSIZE) [..] 'd4: end_address = {AxADDR[ADDR_WIDTH-1:4], 4'h0}
	  * {AxLEN, 4'h0} [...] for each AxSIZE, the same can be achieved by a simple
	  * comb logic: always_comb end_addr = AxADDR + (AxLEN << AxSIZE).
	  * Finally we make sure that AWADDR-1:12 bits are stable,
	  * otherwise this is a violation. */
	 always_comb begin
	    end_addr = (AWADDR + (AWLEN << AWSIZE));
	    aw_4KB_boundary = AWADDR[cfg.ADDRESS_WIDTH-1:12] == end_addr[cfg.ADDRESS_WIDTH-1:12];
	 end
      end // if (cfg.ADDRESS_WIDTH > 12)
   endgenerate

   logic m_bit;
   logic ra_bit;
   logic wa_bit;

   always_comb begin
      // Modifiable bit (renamed from <cacheable> (AXI3)), see A4.3.1
      m_bit = AWCACHE[1];
      // Read-allocate bit
      ra_bit = AWCACHE[2];
      // Write-allocate bit
      wa_bit = AWCACHE[3];
   end


   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *            Section B1.1: Definition of AXI4-Lite                *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.PROTOCOL_TYPE == AXI4LITE) begin
	 // Configure the AXI4-Lite checker unsupported signals.
         cp_AW_unsupported_axi4l: assume property(disable iff (!ARESETn) axi4_lite_unsupported_sig(AW_unsupported_sig))
           else $error("Violation: For AW in AXI4-Lite, only signals described in B1.1 are",
                       "required or supported (B1.1 Definition of AXI4-Lite, pB1-126).");
         // Guard correct AXI4-Lite DATA_WIDTH since the parameter is used here.
         if(cfg.CHECK_PARAMETERS == 1) begin
            ap_AW_AXI4LITE_DATAWIDTH: assert property(axi4l_databus_width(cfg.DATA_WIDTH))
              else $error("Violation: AXI4-Lite supports a data bus width of 32-bit or 64-bit",
                          "(B.1 Definition of AXI4-Lite, pB1-126).");
         end
      end
   endgenerate

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		                   AWID                               *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */
   generate
      if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
	 if(cfg.INTERFACE_REQS == 1'b1) begin
	    if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	       ap_AW_STABLE_AWID: assert property(disable iff(!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWID))
		 else $error("Violation: Once the master has asserted AWVALID, data and control information",
			     "from master must remain stable [AWID] until AWREADY is asserted",
			     "(A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	       if(cfg.ENABLE_XPROP) begin
		  ap_AW_AWID_X: assert property(disable iff(!ARESETn) valid_information(AWVALID, AWID))
		    else $error("Violation : The source can assert the [AW]VALID signal only when it",
				"drives valid address and control information (A3.2.2 Channel signaling",
				"requirements pA3-40).");
	       end
	    end
	    else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
	       cp_AW_STABLE_AWID: assume property(disable iff(!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWID))
		 else $error("Violation: Once the master has asserted AWVALID, data and control information",
			     "from master must remain stable [AWID] until AWREADY is asserted",
			     "(A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	       if(cfg.ENABLE_XPROP) begin
		  cp_AW_AWID_X: assume property(disable iff(!ARESETn) valid_information(AWVALID, AWID))
		    else $error("Violation : The source can assert the [AW]VALID signal only when it",
				"drives valid address and control information (A3.2.2 Channel signaling",
				"requirements pA3-40).");
	       end
	    end
	 end
      end
   endgenerate

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		                  AWADDR                              *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */
   generate
      if(cfg.INTERFACE_REQS == 1'b1) begin
	 if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	    ap_AW_STABLE_AWADDR: assert property(disable iff(!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWADDR))
              else $error("Violation: Once the master has asserted AWVALID, data and control information",
			  "from master must remain stable [AWADDR] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
	       ap_AW_AWADDR_X: assert property(disable iff(!ARESETn) valid_information(AWVALID, AWADDR))
		 else $error("Violation : The source can assert the [AW]VALID signal only when it",
			     "drives valid address and control information (A3.2.2 Channel signaling",
			     "requirements pA3-40).");
	    end
	 end
	 else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
	    cp_AW_STABLE_AWADDR: assume property(disable iff(!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWADDR))
              else $error("Violation: Once the master has asserted AWVALID, data and control information",
			  "from master must remain stable [AWADDR] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
	       cp_AW_AWADDR_X: assume property(disable iff(!ARESETn) valid_information(AWVALID, AWADDR))
		 else $error("Violation : The source can assert the [AW]VALID signal only when it",
			     "drives valid address and control information (A3.2.2 Channel signaling",
			     "requirements pA3-40).");
	    end
	 end
      end

      if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
	 if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	    if(cfg.ADDRESS_WIDTH > 12) begin
	       ap_AW_AWADDR_BOUNDARY_4KB: assert property(disable iff(!ARESETn) burst_cache_line_boundary(AWVALID, AWBURST, aw_4KB_boundary))
		 else $error("Violation: A write burst must not cross a 4KB address boundary (A3.4.1 Address structure, pA3-46).");
	    end
	    if(BURST_SIZE_MAX >= 1 && cfg.INTERFACE_REQS == 1'b1) begin
	       ap_AW_ADDRESS_ALIGNMENT: assert property(disable iff(!ARESETn) start_address_align(AWVALID, AWBURST, AWADDR[6:0], AWSIZE))
		 else $error("Violation: The start address must be aligned to the size of each transfer",
			     "(A3.4.1 Address structure, pA3-48).");
	    end
	 end
	 else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
	    if(cfg.ADDRESS_WIDTH > 12) begin
	       cp_AW_AWADDR_BOUNDARY_4KB: assume property(disable iff(!ARESETn) burst_cache_line_boundary(AWVALID, AWBURST, aw_4KB_boundary))
		 else $error("Violation: A write burst must not cross a 4KB address boundary (A3.4.1 Address structure, pA3-46).");
	    end
	    if(BURST_SIZE_MAX >= 1 && cfg.INTERFACE_REQS == 1'b1) begin
	       cp_AW_ADDRESS_ALIGNMENT: assume property(disable iff(!ARESETn) start_address_align(AWVALID, AWBURST, AWADDR[6:0], AWSIZE))
		 else $error("Violation: The start address must be aligned to the size of each transfer",
			     "(A3.4.1 Address structure, pA3-48).");
	    end
	 end
      end
   endgenerate

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		                   AWLEN                              *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */
   generate
      if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	 if(cfg.CHECK_PARAMETERS) begin
	    ap_AW_AWLEN_MAX: assert property(AWLEN < WRITE_BURST_MAX)
	      else $error("Violation: Parameter WRITE_BURST_MAX determines the max burst lenght capability of",
			  "the DUT, and cannot issue a transaction of AWLEN > WRITE_BURST_MAX.");
	    ap_AW_AWLEN_MAX_WR_BURST_LEN: assert property(AWVALID |-> AWLEN < cfg.MAX_WR_LENGTH)
	      else $error("Violation: Parameter MAX_WR_LENGTH determines the exact number of transfers in a",
			  "burst. The DUT should honor this setting or the user must increase the value of it.");
	 end
	 if(cfg.INTERFACE_REQS) begin
	    ap_AW_STABLE_AWLEN: assert property(disable iff(!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWLEN))
              else $error("Violation: Once the master has asserted AWVALID, data and control information",
			  "from master must remain stable [AWLEN] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
	       ap_AW_AWLEN_X: assert property(disable iff(!ARESETn) valid_information(AWVALID, AWLEN))
		 else $error("Violation : The source can assert the [AW]VALID signal only when it",
			     "drives valid address and control information (A3.2.2 Channel signaling",
			     "requirements pA3-40).");
	    end
	 end
	 ap_AW_VALID_WRAP_BURST: assert property(disable iff(!ARESETn) valid_wrap_burst_length(AWVALID, AWBURST, AWLEN))
           else $error("Violation: For wrapping bursts, the burst length must be 2, 4, 8 or 16 (A3.4.1 Address structure, pA3-46).");
	 ap_AW_VALID_LEN_FIXED: assert property(disable iff(!ARESETn) supported_burst_transfer(AWVALID, AWBURST, FIXED, AW_FIXED_len))
           else $error("Violation: Support for FIXED burst type in AXI4 remains at 1 to 16 transfers (A3.4.1 Address structure, pA3-46).");
	 if(cfg.EXCLUSIVE_ACCESS) begin
	    ap_AW_VALID_BURST_LEN_EXCLUSIVE: assert property(disable iff(!ARESETn) valid_burst_len_exclusive(AWVALID, AWLOCK, AWLEN))
              else $error("Violation: In AXI4, the burst length for an exclusive access must not exceed 16 transfers",
			  "(A7.2.4 Exclusive access restrictions, pA7-97).");
	 end
      end
      else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
	 if(cfg.CHECK_PARAMETERS) begin
	    cp_AW_AWLEN_MAX: assume property(AWLEN < WRITE_BURST_MAX)
	      else $error("Violation: Parameter WRITE_BURST_MAX determines the max burst lenght capability of",
			  "the DUT, and cannot issue a transaction of AWLEN > WRITE_BURST_MAX.");
	    cp_AW_AWLEN_MAX_WR_BURST_LEN: assume property(AWVALID |-> AWLEN < cfg.MAX_WR_LENGTH)
	      else $error("Violation: Parameter MAX_WR_LENGTH determines the exact number of transfers in a",
			  "burst. The DUT should honor this setting or the user must increase the value of it.");
	 end
	 if(cfg.INTERFACE_REQS) begin
	    cp_AW_STABLE_AWLEN: assume property(disable iff(!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWLEN))
              else $error("Violation: Once the master has asserted AWVALID, data and control information",
			  "from master must remain stable [AWLEN] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
	       cp_AW_AWLEN_X: assume property(disable iff(!ARESETn) valid_information(AWVALID, AWLEN))
		 else $error("Violation : The source can assert the [AW]VALID signal only when it",
			     "drives valid address and control information (A3.2.2 Channel signaling",
			     "requirements pA3-40).");
	    end
	 end
	 cp_AW_VALID_WRAP_BURST: assume property(disable iff(!ARESETn) valid_wrap_burst_length(AWVALID, AWBURST, AWLEN))
           else $error("Violation: For wrapping bursts, the burst length must be 2, 4, 8 or 16 (A3.4.1 Address structure, pA3-46).");
	 cp_AW_VALID_LEN_FIXED: assume property(disable iff(!ARESETn) supported_burst_transfer(AWVALID, AWBURST, FIXED, AW_FIXED_len))
           else $error("Violation: Support for FIXED burst type in AXI4 remains at 1 to 16 transfers (A3.4.1 Address structure, pA3-46).");
         if(cfg.EXCLUSIVE_ACCESS) begin
            cp_AW_VALID_BURST_LEN_EXCLUSIVE: assume property(disable iff(!ARESETn) valid_burst_len_exclusive(AWVALID, AWLOCK, AWLEN))
              else $error("Violation: In AXI4, the burst length for an exclusive access must not exceed 16 transfers",
                          "(A7.2.4 Exclusive access restrictions, pA7-97).");
	 end
      end // if (cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT})
   endgenerate
   
   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                             AWSIZE                              *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
         if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	    if(cfg.INTERFACE_REQS == 1'b1) begin
               ap_AW_STABLE_AWSIZE: assert property(disable iff(!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWSIZE))
		 else $error("Violation: Once the master has asserted AWVALID, data and control information",
                             "from master must remain stable [AWSIZE] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	       if(cfg.ENABLE_XPROP) begin
		  ap_AW_AWSIZE_X: assert property(disable iff(!ARESETn) valid_information(AWVALID, AWSIZE))
		    else $error("Violation : The source can assert the [AW]VALID signal only when it",
				"drives valid address and control information (A3.2.2 Channel signaling",
				"requirements pA3-40).");
	       end
	    end
	    ap_AW_CORRECT_BURST_SIZE: assert property(disable iff(!ARESETn) burst_size_within_width_boundary(AWVALID, AWSIZE, STRB_WIDTH))
	      else $error("Violation: The size of any transfer must not exceed the data bus width of either agent in the transaction.",
			  "(A3.4.1 Address structure, Burst size, pA3-47).");
	 end
	 else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
	    if(cfg.INTERFACE_REQS) begin
	       cp_AW_STABLE_AWSIZE: assume property(disable iff(!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWSIZE))
		 else $error("Violation: Once the master has asserted AWVALID, data and control information",
			     "from master must remain stable [AWSIZE] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	       if(cfg.ENABLE_XPROP) begin
		  cp_AW_AWSIZE_X: assume property(disable iff(!ARESETn) valid_information(AWVALID, AWSIZE))
		    else $error("Violation : The source can assert the [AW]VALID signal only when it",
				"drives valid address and control information (A3.2.2 Channel signaling",
				"requirements pA3-40).");
	       end
	       cp_AW_CORRECT_BURST_SIZE: assume property(disable iff(!ARESETn) burst_size_within_width_boundary(AWVALID, AWSIZE, STRB_WIDTH))
		 else $error("Violation: The size of any transfer must not exceed the data bus width of either agent in the transaction.",
			     "(A3.4.1 Address structure, Burst size, pA3-47).");
	    end
	 end
      end
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                              AWBURST                            *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
         if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	    if(cfg.INTERFACE_REQS == 1'b1) begin
	       ap_AW_STABLE_AWBURST: assert property(disable iff(!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWBURST))
		 else $error("Violation: Once the master has asserted AWVALID, data and control information",
                             "from master must remain stable [AWBURST] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	       if(cfg.ENABLE_XPROP) begin
		  ap_AW_AWBURST_X: assert property(disable iff(!ARESETn) valid_information(AWVALID, AWBURST))
		    else $error("Violation : The source can assert the [AW]VALID signal only when it",
				"drives valid address and control information (A3.2.2 Channel signaling",
				"requirements pA3-40).");
	       end
	    end
	    ap_AW_BURST_TYPES: assert property(disable iff(!ARESETn) AWVALID |-> AWBURST != RESERVED)
              else $error("Violation: The AXI protocol defines three burst types, FIXED, INCR and WRAP. RESERVED is undefined",
                          "and therefore not a valid burst (A3.4.1 Address structure, pA3-48, Table A3-3 Burst type encoding).");
         end
         else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
	    if(cfg.INTERFACE_REQS == 1'b1) begin
	       cp_AW_STABLE_AWBURST: assume property(disable iff(!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWBURST))
		 else $error("Violation: Once the master has asserted AWVALID, data and control information",
                             "from master must remain stable [AWBURST] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	       if(cfg.ENABLE_XPROP) begin
		  cp_AW_AWBURST_X: assume property(disable iff(!ARESETn) valid_information(AWVALID, AWBURST))
		    else $error("Violation : The source can assert the [AW]VALID signal only when it",
				"drives valid address and control information (A3.2.2 Channel signaling",
				"requirements pA3-40).");
	       end
	    end
	    cp_AW_BURST_TYPES: assume property(disable iff(!ARESETn) AWVALID |-> AWBURST != RESERVED)
              else $error("Violation: The AXI protocol defines three burst types, FIXED, INCR and WRAP. RESERVED is undefined",
                          "and therefore not a valid burst (A3.4.1 Address structure, pA3-48, Table A3-3 Burst type encoding).");
	 end
      end // if (cfg.PROTOCOL_TYPE == AXI4FULL)
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                             AWLOCK                              *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
	 if(cfg.INTERFACE_REQS == 1'b1) begin
	    if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	       ap_AW_STABLE_AWLOCK: assert property(disable iff(!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWLOCK))
		 else $error("Violation: Once the master has asserted AWVALID, data and control information",
                             "from master must remain stable [AWLOCK] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	       if(cfg.ENABLE_XPROP) begin
		  ap_AW_AWLOCK_X: assert property(disable iff(!ARESETn) valid_information(AWVALID, AWLOCK))
		    else $error("Violation : The source can assert the [AW]VALID signal only when it",
				"drives valid address and control information (A3.2.2 Channel signaling",
				"requirements pA3-40).");
	       end
	    end
	    else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
	       cp_AW_STABLE_AWLOCK: assume property(disable iff(!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWLOCK))
		 else $error("Violation: Once the master has asserted AWVALID, data and control information",
                             "from master must remain stable [AWLOCK] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	       if(cfg.ENABLE_XPROP) begin
		  cp_AW_AWLOCK_X: assume property(disable iff(!ARESETn) valid_information(AWVALID, AWLOCK))
		    else $error("Violation : The source can assert the [AW]VALID signal only when it",
				"drives valid address and control information (A3.2.2 Channel signaling",
				"requirements pA3-40).");
	       end
	    end
	 end
      end
      if(cfg.PROTOCOL_TYPE == AXI4LITE) begin
         if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	    ap_AW_UNSUPPORTED_EXCLUSIVE: assert property(disable iff(!ARESETn) unsupported_exclusive_access(AWVALID, AWLOCK, EXCLUSIVE))
              else $error("Violation: Exclusive read accesses are not supported in AXI4 Lite",
                          "(Definition of AXI4-Lite, pB1-126).");
         end
         else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
	    cp_AW_UNSUPPORTED_EXCLUSIVE: assume property(disable iff(!ARESETn) unsupported_exclusive_access(AWVALID, AWLOCK, EXCLUSIVE))
              else $error("Violation: Exclusive read accesses are not supported in AXI4 Lite",
                          "(Definition of AXI4-Lite, pB1-126).");
         end
      end // if (cfg.PROTOCOL_TYPE == AXI4LITE)
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                             AWCACHE                             *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
	 if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	    if(cfg.INTERFACE_REQS == 1'b1) begin
	       ap_AW_STABLE_AWCACHE: assert property(disable iff(!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWCACHE))
		 else $error("Violation: Once the master has asserted AWVALID, data and control information",
			     "from master must remain stable [AWCACHE] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	       if(cfg.ENABLE_XPROP) begin
		  ap_AW_AWCACHE_X: assert property(disable iff(!ARESETn) valid_information(AWVALID, AWCACHE))
		    else $error("Violation : The source can assert the [AW]VALID signal only when it",
				"drives valid address and control information (A3.2.2 Channel signaling",
				"requirements pA3-40).");
	       end
	    end
	    ap_AW_MEMORY_TYPE_ENCODING: assert property(disable iff(!ARESETn) memory_type_encoding(AWVALID, AWCACHE))
	      else $error("Violation: For memory types, all values not shown in Table A4-5 are reserved,",
			  "(A4.4 Memory types, pA4-67, Table A4-5 Memory type encoding, pA4-67");
	    ap_AW_NON_CACHEABLE: assert property(AWVALID && !m_bit |-> {ra_bit, wa_bit} == 2'b00)
	      else $error("Violation: When Modifiable bit is not asserted, Read-allocate and Write-allocate bits",
			  "cannot indicate a cacheable transaction (A4.4 Memory types, Table A4-5 Memory type encoding, pA4-67).");
	    if(cfg.EXCLUSIVE_ACCESS) begin
	       ap_AW_EXCLUSIVE_NON_CACHEABLE: assert property(AWVALID && AWLOCK == EXCLUSIVE |-> ({ra_bit, wa_bit} == 2'b00))
		 else $error("Violation: An exclusive access must not have an AWCACHE value that indicates that",
			     "the transaction is Cacheable (A7.2.4 Exclusive access restrictions, pA7-97).");
	    end
	 end
	 else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
	    if(cfg.INTERFACE_REQS == 1'b1) begin
               cp_AW_STABLE_AWCACHE: assume property(disable iff(!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWCACHE))
		 else $error("Violation: Once the master has asserted AWVALID, data and control information",
			     "from master must remain stable [AWCACHE] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	       if(cfg.ENABLE_XPROP) begin
		  cp_AW_AWCACHE_X: assume property(disable iff(!ARESETn) valid_information(AWVALID, AWCACHE))
		    else $error("Violation : The source can assert the [AW]VALID signal only when it",
				"drives valid address and control information (A3.2.2 Channel signaling",
				"requirements pA3-40).");
	       end
	    end
	    cp_AW_MEMORY_TYPE_ENCODING: assume property(disable iff(!ARESETn) memory_type_encoding(AWVALID, AWCACHE))
	      else $error("Violation: For memory types, all values not shown in Table A4-5 are reserved,",
			  "(A4.4 Memory types, pA4-67, Table A4-5 Memory type encoding");
	    cp_AW_NON_CACHEABLE: assume property(AWVALID && !m_bit |-> {ra_bit, wa_bit} == 2'b00)
	      else $error("Violation: When Modifiable bit is not asserted, Read-allocate and Write-allocate bits",
			  "cannot indicate a cacheable transaction (A4.4 Memory types, Table A4-5 Memory type encoding, pA4-67).");
	    if(cfg.EXCLUSIVE_ACCESS) begin
	       cp_AW_EXCLUSIVE_NON_CACHEABLE: assume property(AWVALID && AWLOCK == EXCLUSIVE |-> ({ra_bit, wa_bit} == 2'b00))
		 else $error("Violation: An exclusive access must not have an AWCACHE value that indicates that",
			     "the transaction is Cacheable (A7.2.4 Exclusive access restrictions, pA7-97).");
	    end
	 end
      end // if (cfg.PROTOCOL_TYPE == AXI4FULL)
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                             AWPROT                              *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.INTERFACE_REQS == 1'b1) begin
	 if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	    ap_AW_STABLE_AWPROT: assert property(disable iff(!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWPROT))
              else $error("Violation: Once the master has asserted AWVALID, data and control information",
			  "from master must remain stable [AWPROT] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
	       ap_AW_AWPROT_X: assert property(disable iff(!ARESETn) valid_information(AWVALID, AWPROT))
		 else $error("Violation : The source can assert the [AW]VALID signal only when it",
			     "drives valid address and control information (A3.2.2 Channel signaling",
			     "requirements pA3-40).");
	    end
	 end
	 else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
	    cp_AW_STABLE_AWPROT: assume property(disable iff(!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWPROT))
              else $error("Violation: Once the master has asserted AWVALID, data and control information",
			  "from master must remain stable [AWPROT] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
	       cp_AW_AWPROT_X: assume property(disable iff(!ARESETn) valid_information(AWVALID, AWPROT))
		 else $error("Violation : The source can assert the [AW]VALID signal only when it",
			     "drives valid address and control information (A3.2.2 Channel signaling",
			     "requirements pA3-40).");
	    end
	 end
      end
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                             AWQOS                               *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.PROTOCOL_TYPE == AXI4FULL && cfg.INTERFACE_REQS == 1'b1) begin
	 if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	    ap_AW_STABLE_AWQOS: assert property(disable iff(!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWQOS))
	      else $error("Violation: Once the master has asserted AWVALID, data and control information",
			  "from master must remain stable [AWQOS] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
	       ap_AW_AWQOS_X: assert property(disable iff(!ARESETn) valid_information(AWVALID, AWQOS))
		 else $error("Violation : The source can assert the [AW]VALID signal only when it",
			     "drives valid address and control information (A3.2.2 Channel signaling",
			     "requirements pA3-40).");
	    end
	 end
	 else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
            cp_AW_STABLE_AWQOS: assume property(disable iff(!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWQOS))
	      else $error("Violation: Once the master has asserted AWVALID, data and control information",
			  "from master must remain stable [AWQOS] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
	       cp_AW_AWQOS_X: assume property(disable iff(!ARESETn) valid_information(AWVALID, AWQOS))
		 else $error("Violation : The source can assert the [AW]VALID signal only when it",
			     "drives valid address and control information (A3.2.2 Channel signaling",
			     "requirements pA3-40).");
	    end
	 end
      end
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                             AWREGION                            *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.PROTOCOL_TYPE == AXI4FULL && cfg.INTERFACE_REQS == 1'b1) begin
	 if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	    ap_AW_STABLE_AWREGION: assert property(disable iff(!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWREGION))
	      else $error("Violation: Once the master has asserted AWVALID, data and control information",
			  "from master must remain stable [AWREGION] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
	       ap_AW_AWREGION_X: assert property(disable iff(!ARESETn) valid_information(AWVALID, AWREGION))
		 else $error("Violation : The source can assert the [AW]VALID signal only when it",
			     "drives valid address and control information (A3.2.2 Channel signaling",
			     "requirements pA3-40).");
	    end
	 end
	 else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
            cp_AW_STABLE_AWREGION: assume property(disable iff(!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWREGION))
	      else $error("Violation: Once the master has asserted AWVALID, data and control information",
			  "from master must remain stable [AWREGION] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
	       cp_AW_AWREGION_X: assume property(disable iff(!ARESETn) valid_information(AWVALID, AWREGION))
		 else $error("Violation : The source can assert the [AW]VALID signal only when it",
			     "drives valid address and control information (A3.2.2 Channel signaling",
			     "requirements pA3-40).");
	    end
	 end
      end
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                             AWUSER                              *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.PROTOCOL_TYPE == AXI4FULL && cfg.INTERFACE_REQS == 1'b1) begin
	 if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	    ap_AW_STABLE_AWUSER: assert property(disable iff(!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWUSER))
	      else $error("Violation: Once the master has asserted AWVALID, data and control information",
			  "from master must remain stable [AWUSER] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
	       ap_AW_AWUSER_X: assert property(disable iff(!ARESETn) valid_information(AWVALID, AWUSER))
		 else $error("Violation : The source can assert the [AW]VALID signal only when it",
			     "drives valid address and control information (A3.2.2 Channel signaling",
			     "requirements pA3-40).");
	    end
	 end
	 else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
	    cp_AW_STABLE_AWUSER: assume property(disable iff(!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWUSER))
	      else $error("Violation: Once the master has asserted AWVALID, data and control information",
			  "from master must remain stable [AWUSER] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
	       cp_AW_AWUSER_X: assume property(disable iff(!ARESETn) valid_information(AWVALID, AWUSER))
		 else $error("Violation : The source can assert the [AW]VALID signal only when it",
			     "drives valid address and control information (A3.2.2 Channel signaling",
			     "requirements pA3-40).");
	    end
	 end
      end
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                             AWVALID                             *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.OPTIONAL_RESET == 1 && cfg.INTERFACE_REQS == 1) begin
	 if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	    ap_AW_EXIT_RESET: assert property(exit_from_reset(ARESETn, AWVALID))
              else $error("Violation: AWVALID must be low for the first clock edge",
                          "after ARESETn goes high (A3.2.1 Reset, pA3-38, Figure A3-1).");
	 end
	 else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
	    cp_AW_EXIT_RESET: assume property(exit_from_reset(ARESETn, AWVALID))
              else $error("Violation: AWVALID must be low for the first clock edge",
                          "after ARESETn goes high (A3.2.1 Reset, pA3-38, Figure A3-1).");
	 end
      end
      if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	 ap_AW_AWVALID_until_AWREADY: assert property(disable iff(!ARESETn) valid_before_handshake(AWVALID, AWREADY))
           else $error("Violation: Once AWVALID is asserted it must remain asserted until the handshake",
                       "occurs (A3.2.1 Handshake process, pA3-39).");
	 if(cfg.ENABLE_XPROP) begin
	    ap_AW_AWVALID_X: assert property(disable iff(!ARESETn) valid_information(ARESETn, AWVALID))
	      else $error("Violation : The source can assert the [AW]VALID signal only when it",
			  "drives valid address and control information (A3.2.2 Channel signaling",
			  "requirements pA3-40).");
	 end
      end
      else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
	 cp_AW_AWVALID_until_AWREADY: assume property(disable iff(!ARESETn) valid_before_handshake(AWVALID, AWREADY))
           else $error("Violation: Once AWVALID is asserted it must remain asserted until the handshake",
                       "occurs (A3.2.1 Handshake process, pA3-39).");
	 if(cfg.ENABLE_XPROP) begin
	    cp_AW_AWVALID_X: assume property(disable iff(!ARESETn) valid_information(ARESETn, AWVALID))
	      else $error("Violation : The source can assert the [AW]VALID signal only when it",
			  "drives valid address and control information (A3.2.2 Channel signaling",
			  "requirements pA3-40).");
	 end
      end
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                             AWREADY                             *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, MONITOR}) begin
	 if(cfg.INTERFACE_REQS == 1'b1) begin
	    if(cfg.ENABLE_XPROP) begin
	       ap_AW_AWREADY_X: assert property(disable iff(!ARESETn) valid_information(ARESETn, AWREADY))
		 else $error("Violation : The source can assert the [AW]VALID signal only when it",
			     "drives valid address and control information (A3.2.2 Channel signaling",
			     "requirements pA3-40).");
	    end
	 end
	 else if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, CONSTRAINT}) begin
	    if(cfg.ENABLE_XPROP) begin
	       cp_AW_AWREADY_X: assume property(disable iff(!ARESETn) valid_information(ARESETn, AWREADY))
		 else $error("Violation : The source can assert the [AW]VALID signal only when it",
			     "drives valid address and control information (A3.2.2 Channel signaling",
			     "requirements pA3-40).");
	    end
	 end
      end
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                        AMBA Recommended                         *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.ARM_RECOMMENDED == 1) begin
	 if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, MONITOR}) begin
	    ap_AW_READY_MAXWAIT: assert property(disable iff(!ARESETn) handshake_max_wait(AWVALID, AWREADY, cfg.MAXWAIT))
              else $error("Violation: AWREADY should be asserted within MAXWAIT cycles of AWVALID being asserted (AMBA recommended).");
	 end
	 else if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, CONSTRAINT}) begin
	    cp_AW_READY_MAXWAIT: assume property(disable iff(!ARESETn) handshake_max_wait(AWVALID, AWREADY, cfg.MAXWAIT))
              else $error("Violation: AWREADY should be asserted within MAXWAIT cycles of AWVALID being asserted (AMBA recommended).");
	 end
      end
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *              Covers To Maximise Debug Information               *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   // Witnessing scenarios stated in the AMBA AXI4 spec
   generate
      if(cfg.ENABLE_COVER == 1) begin: witness
	 // For witness
	 let AW_request_accepted = AWVALID && AWREADY;

	 // Single handshake
	 sequence aw_handshake_cond(cond);
	    AWVALID ##0 AWREADY ##0 cond;
	 endsequence // aw_burst_size

	 /* This sequence looks for two handshakes
	  * and is used to witness a transaction
	  * process where two request are made
	  * with different ID. */
	 sequence aw_two_handshakes;
	    AWVALID ##0 AWREADY ##1
	    AWVALID ##0 AWREADY;
	 endsequence // aw_two_handshakes

	 /* ,         ,                                                     *
	  * |\\\\ ////|  "The length of the burst must be 2, 4, 8, or 16    *
	  * | \\\V/// |   transfers".                                       *
	  * |  |~~~|  |                                                     *
	  * |  |===|  |   Ref: A3.4 Transaction structure, Burst type WRAP, *
	  * |  |A  |  |   pA3-48.                                           *
	  * |  | X |  |                                                     *
	  *  \ |  I| /                                                      *
	  *   \|===|/                                                       *
	  *    '---'                                                        */
	 sequence wrapping_burst_len(l);
	    AWVALID ##0 AWREADY ##0 AWBURST == WRAP
	    ##0 AWLEN == l;
	 endsequence // wrapping_burst_len

	 /*            ><><><><><><><><><><><><><><><><><><><><             *
	  *          Section A3.4.3 Data read and write structure           *
	  *            ><><><><><><><><><><><><><><><><><><><><             */

	 /* ,         ,                                                     *
	  * |\\\\ ////|  "AXI supports unaligned transfers. [...],          *
	  * | \\\V/// |   A source can: use the low-order address lines to  *
	  * |  |~~~|  |   signal an unaligned start address".               *
	  * |  |===|  |   Ref: A3.4.3 Address structure, Unaligned,         *
	  * |  |A  |  |        transfers, pA3-54.                           *
	  * |  | X |  |                                                     *
	  *  \ |  I| /                                                      *
	  *   \|===|/                                                       *
	  *    '---'                                                        */
	 sequence unaligned_transfer(a, t);
	    AWVALID ##0 AWREADY ##0 AWSIZE == SIZE2B
	    ##0 AWADDR[a] == 1'b1 ##0 AWBURST == t;
	 endsequence // unaligned_transfer

	 /* ,         ,                                                     *
	  * |\\\\ ////|  "The number of bytes to be transferred in an       *
	  * | \\\V/// |   exclusive access burst must be a power of 2, that *
	  * |  |~~~|  |   is, 1, 2, 4, 8, 16, 32, 64, or 128 bytes".        *
	  * |  |===|  |   Ref: A7.2.4 Exclusive access restrictions, pA7-97 *
	  * |  |A  |  |                                                     *
	  * |  | X |  |                                                     *
	  *  \ | I | /	                                                    *
	  *   \|===|/							    *
	  *    '---'							    */
	 sequence exclusive_access_byte_transfer(size, len);
	    AWVALID ##0 AWREADY ##0 AWLOCK == EXCLUSIVE
	    ##0 AWSIZE == size ##0 AWLEN == len;
	 endsequence // exclusive_access_byte_transfer

	 /*		 ><><><><><><><><><><><><><><><><><><><><             *
	  *		                   AWID                               *
	  *		 ><><><><><><><><><><><><><><><><><><><><	      */
	 if(cfg.VERIFY_AGENT_TYPE != DESTINATION) begin
	    if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
	       wp_TWO_TRANSACTIONS_DIFFERENT_AWID: cover property(aw_two_handshakes ##0 AWID != $past(AWID))
		 $info("Witnessed: Two transactions tagged with different ID.");
	       for(genvar idx = 0; idx < (2**cfg.ID_WIDTH); idx++) begin
		  wp_AWID_TAG_NUMBER: cover property(aw_handshake_cond(AWID == idx))
		    $info("Witnessed: Transaction ID covering all possible values derived by ID_WIDTH parameter.");
	       end
	    end
	 end

	 /*		 ><><><><><><><><><><><><><><><><><><><><             *
	  *		                  AWADDR                              *
	  *		 ><><><><><><><><><><><><><><><><><><><><	      */
	 if(cfg.VERIFY_AGENT_TYPE != DESTINATION) begin
	    if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
	       wp_UNALIGNED_TRANSFERS_FIXED_BURST: cover property(unaligned_transfer(0, FIXED))
		 $info("Witnessed: Source signaling an unaligned transfer with burst type FIXED (pA3-54).");
	       wp_UNALIGNED_TRANSFERS_INCR_BURST: cover property(unaligned_transfer(1, INCR))
		 $info("Witnessed: Source signaling an unaligned transfer with burst type INCR (pA3-54).");
	    end
	 end

	 /*		 ><><><><><><><><><><><><><><><><><><><><             *
	  *		                   AWLEN                              *
	  *		 ><><><><><><><><><><><><><><><><><><><><	      */
	 if(cfg.VERIFY_AGENT_TYPE != DESTINATION) begin
	    if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
	       for(genvar i = 0; i < $clog2(cfg.MAX_WR_LENGTH); i++) begin: write_transaction_len
		  wp_AW_LEN_TRANSFERS: cover property(AW_request_accepted && AWLEN == i)
		  $info("Witnessed: Burst lenght of size 0 to MAX_WR_LENGTH",
			"(A3.4.1 Address strucutre, pA3-46).");
	       end
	       /* TODO: Bring here outstanding transaction counters to create covers for
		* first transactions with different AWLEN values. */
	       for(genvar len = 2; len <= cfg.MAX_WR_LENGTH; len = len * 2) begin
		  wp_WRAPPING_BURST_LEN: cover property(wrapping_burst_len((len -  1'b1)))
		    $info("Witnessed: Wrapping burst len of cfg.MAX_WR_LENGTH transfers.");
	       end
	    end // if (cfg.PROTOCOL_TYPE == AXI4FULL)
	 end // if (cfg.VERIFY_AGENT_TYPE != DESTINATION)

	 /*            ><><><><><><><><><><><><><><><><><><><><             *
	  *                             AWSIZE                              *
	  *            ><><><><><><><><><><><><><><><><><><><><             */
	 if(cfg.VERIFY_AGENT_TYPE != DESTINATION) begin
	    if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
	       /* As stated in Table A3-2 Burst size encoding,
		* BURST_SIZE_MAX (calculated with WSTRB) is the
		* maximum number of bytes to transfer in each beat.
		* This sequence helps to check that the model can
		* accept such burst transfer sizes. */
	       for(genvar j = 0; j <= BURST_SIZE_MAX; j++) begin
		  wp_MAX_BURST_SIZE: cover property(disable iff(!ARESETn) aw_handshake_cond(AWSIZE == j))
		    $info("Witnessed: AWSIZE signaling BURST_SIZE_MAX bytes in transfer capability");
	       end
	    end // if (cfg.PROTOCOL_TYPE == AXI4FULL)
	 end // if (cfg.VERIFY_AGENT_TYPE != DESTINATION)

	 /*            ><><><><><><><><><><><><><><><><><><><><             *
	  *                              AWBURST                            *
	  *            ><><><><><><><><><><><><><><><><><><><><             */
	 if(cfg.VERIFY_AGENT_TYPE != DESTINATION) begin
	    if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
	       wp_BURST_FIXED: cover property(disable iff(!ARESETn) aw_handshake_cond(AWBURST == FIXED))
		 $info("Witnessed: Burst type FIXED");
	       wp_BURST_INCR: cover property(disable iff(!ARESETn) aw_handshake_cond(AWBURST == INCR))
		 $info("Witnessed: Burst type INCR");
	       wp_BURST_WRAP: cover property(disable iff(!ARESETn) aw_handshake_cond(AWBURST == WRAP))
		 $info("Witnessed: Burst type WRAP");
	    end
	 end

	 /*            ><><><><><><><><><><><><><><><><><><><><             *
	  *                             AWLOCK                              *
	  *            ><><><><><><><><><><><><><><><><><><><><             */
	 if(cfg.VERIFY_AGENT_TYPE != DESTINATION) begin
	    if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
	       wp_AWLOCK_NORMAL: cover property(disable iff(!ARESETn) aw_handshake_cond(AWLOCK == NORMAL))
		 $info("Witnessed: Locked transaction type NORMAL");
	       if(cfg.EXCLUSIVE_ACCESS) begin
		  wp_AWLOCK_EXCLUSIVE: cover property(disable iff(!ARESETn) aw_handshake_cond(AWLOCK == EXCLUSIVE))
		    $info("Witnessed: Locked transaction type EXCLUSIVE");
		  for(genvar i = 0; i <= BURST_SIZE_MAX; i++) begin: transfer_size
		     wp_EXCLUSIVE_ACCESS_BYTE_TRANSFER_SIZE1B: cover property(exclusive_access_byte_transfer(SIZE1B, ((2**i)-1)))
		       $info("Witnessed: Atomic transfer with AWSIZE = SIZE1B and AWLEN = 1 to 16.");
		     wp_EXCLUSIVE_ACCESS_BYTE_TRANSFER_SIZE2B: cover property(exclusive_access_byte_transfer(SIZE2B, ((2**i)-1)))
		       $info("Witnessed: Atomic transfer with AWSIZE = SIZE2B and AWLEN = 2 to 32.");
		     wp_EXCLUSIVE_ACCESS_BYTE_TRANSFER_SIZE4B: cover property(exclusive_access_byte_transfer(SIZE4B, ((2**i)-1)))
		       $info("Witnessed: Atomic transfer with AWSIZE = SIZE4B and AWLEN = 4 to 64.");
		     wp_EXCLUSIVE_ACCESS_BYTE_TRANSFER_SIZE8B: cover property(exclusive_access_byte_transfer(SIZE8B, ((2**i)-1)))
		       $info("Witnessed: Atomic transfer with AWSIZE = SIZE4B and AWLEN = 8 to 128.");
		  end
	       end // if (cfg.EXCLUSIVE_ACCESS)
	    end // if (cfg.PROTOCOL_TYPE == AXI4FULL)
	 end // if (cfg.VERIFY_AGENT_TYPE != DESTINATION)

	 /*            ><><><><><><><><><><><><><><><><><><><><             *
	  *                             AWCACHE                             *
	  *            ><><><><><><><><><><><><><><><><><><><><             */
	 if(cfg.VERIFY_AGENT_TYPE != DESTINATION) begin
	    if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
	       wp_AWCACHE_NON_BUFFERABLE: cover property(aw_handshake_cond(AWCACHE == 4'h0))
		 $info("Witnessed: AW transaction with Memory type = Device Non-bufferable (Table A4-5, pA4-7).");
	       wp_AWCACHE_BUFFERABLE: cover property(aw_handshake_cond(AWCACHE == 4'h1))
		 $info("Witnessed: AW transaction with Memory type = Device Bufferable (Table A4-5, pA4-7).");
	       wp_AWCACHE_NORMAL_NON_CACHEABLE_NON_BUFFERABLE: cover property(aw_handshake_cond(AWCACHE == 4'h2))
		 $info("Witnessed: AW transaction with Memory type = Normal Non-cacheable Non-bufferable (Table A4-5, pA4-7).");
	       wp_AWCACHE_NORMAL_NON_CACHEABLE_BUFFERABLE: cover property(aw_handshake_cond(AWCACHE == 4'h3))
		 $info("Witnessed: AW transaction with Memory type = Normal Non-cacheable Bufferable (Table A4-5, pA4-7).");
	       wp_AWCACHE_WRITE_THROUGH_NO_ALLOCATE: cover property(aw_handshake_cond(AWCACHE == 4'h6))
		 $info("Witnessed: AW transaction with Memory type = Write-through No-allocate (Table A4-5, pA4-7).");
	       wp_AWCACHE_WRITE_THROUGH_WRITE_ALLOCATE: cover property(aw_handshake_cond(AWCACHE == 4'hA))
		 $info("Witnessed: AW transaction with Memory type = Write-through Write-allocate (Table A4-5, pA4-7).");
	       wp_AWCACHE_WRITE_THROUGH_READ_AND_WRITE_ALLOCATE: cover property(aw_handshake_cond(AWCACHE == 4'hE))
		 $info("Witnessed: AW transaction with Memory type = Write-through Read and Write-allocate (Table A4-5, pA4-7).");
	       wp_AWCACHE_WRITE_BACK_READ_ALLOCATE: cover property(aw_handshake_cond(AWCACHE == 4'h7))
		 $info("Witnessed: AW transaction with Memory type = Write-back Read-allocate (Table A4-5, pA4-7).");
	       wp_AWCACHE_WRITE_BACK_WRITE_ALLOCATE: cover property(aw_handshake_cond(AWCACHE == 4'hB))
		 $info("Witnessed: AW transaction with Memory type = Write-back Write-allocate (Table A4-5, pA4-7).");
	       wp_AWCACHE_WRITE_BACK_READ_AND_WRITE_ALLOCATE: cover property(aw_handshake_cond(AWCACHE == 4'hF))
		 $info("Witnessed: AW transaction with Memory type = Write-back Read and Write-allocate (Table A4-5, pA4-7).");
	       wp_ATOMIC_WRITE_NONCACHEABLE_mbit: cover property(aw_handshake_cond(AWLOCK == EXCLUSIVE && !m_bit))
		 $info("Witnessed: Exclusive (write) access with AWCACHE value indicating non-cacheable (modifiable) transaction",
		       "(A7.2.4 Exclusive access restrictions, pA7-97).");
	    end // if (cfg.PROTOCOL_TYPE == AXI4FULL)
	 end // if (cfg.VERIFY_AGENT_TYPE != DESTINATION)

	 /*            ><><><><><><><><><><><><><><><><><><><><             *
	  *                             AWPROT                              *
	  *            ><><><><><><><><><><><><><><><><><><><><             */
	 if(cfg.VERIFY_AGENT_TYPE != DESTINATION) begin
	    if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
	       wp_AWPROT_UNPRIVILEGED_ACCESS: cover property(aw_handshake_cond(AWPROT[0] == 1'b0))
		 $info("Witnessed: AW access permission: Unprivileged access (Table A4-6, pA4-73).");
	       wp_AWPROT_PRIVILEGED_ACCESS: cover property(aw_handshake_cond(AWPROT[0] == 1'b1))
		 $info("Witnessed: AW access permission: Privileged access (Table A4-6, pA4-73).");
	       wp_AWPROT_SECURE_ACCESS: cover property(aw_handshake_cond(AWPROT[1] == 1'b0))
		 $info("Witnessed: AW access permission: Secure access (Table A4-6, pA4-73).");
	       wp_AWPROT_NON_SECURE_ACCESS: cover property(aw_handshake_cond(AWPROT[1] == 1'b1))
		 $info("Witnessed: AW access permission: Non-secure access (Table A4-6, pA4-73).");
	       wp_AWPROT_DATA_ACCESS: cover property(aw_handshake_cond(AWPROT[2] == 1'b0))
		 $info("Witnessed: AW access permission: Data access (Table A4-6, pA4-73).");
	       wp_AWPROT_INSTRUCTION_ACCESS: cover property(aw_handshake_cond(AWPROT[2] == 1'b1))
		 $info("Witnessed: AW access permission: Instruction access (Table A4-6, pA4-73).");
	    end // if (cfg.PROTOCOL_TYPE == AXI4FULL)
	 end // if (cfg.VERIFY_AGENT_TYPE != DESTINATION)

	 /*            ><><><><><><><><><><><><><><><><><><><><             *
	  *                             AWREADY                             *
	  *            ><><><><><><><><><><><><><><><><><><><><             */
         wp_AWVALID_before_AWREADY: cover property(disable iff (!ARESETn) valid_before_ready(AWVALID, AWREADY))
           $info("Witnessed: Handshake process pA3-39, Figure A3-2 VALID before READY handshake capability.");
         wp_AWREADY_before_AWVALID: cover property(disable iff (!ARESETn) ready_before_valid(AWVALID, AWREADY))
           $info("Witnessed: Handshake process pA3-39, Figure A3-3 READY before VALID handshake capability.");
         wp_AWVALID_with_AWREADY: cover property(disable iff (!ARESETn) valid_with_ready(AWVALID, AWREADY))
           $info("Witnessed: Handshake process pA3-39, Figure A3-4 VALID with READY handshake capability.");
	 if(cfg.MAX_WR_BURSTS > 1) begin
            wp_AW_B2B: cover property(disable iff(!ARESETn) axi4_back_to_back(AWVALID, AWREADY))
              $info("Witnessed: Back to back transaction on AW channel.");
	 end
         wp_AW_WAIT: cover property(disable iff(!ARESETn) axi4_wait_state(AWVALID, AWREADY))
           $info("Witnessed: Wait state during transaction on AW channel.");
         wp_AW_NO_WAIT: cover property(disable iff(!ARESETn) axi4_no_wait_state(AWVALID, AWREADY))
           $info("Witnessed: No wait states during transaction on AW channel.");
      end // block: witness
   endgenerate
endmodule // amba_axi4_write_address_channel
`default_nettype wire

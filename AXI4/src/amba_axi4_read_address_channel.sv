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
module amba_axi4_read_address_channel
  import amba_axi4_protocol_checker_pkg::*;
   #(parameter axi4_checker_params_t cfg =
     '{ID_WIDTH:          4,
       ADDRESS_WIDTH:     32,
       DATA_WIDTH:        32,
       ARUSER_WIDTH:      32,
       MAX_RD_BURSTS:     2,
       MAX_RD_LENGTH:     8,
       VERIFY_AGENT_TYPE: SOURCE,
       PROTOCOL_TYPE:     AXI4LITE,
       CHECK_PARAMETERS:  1,
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
     localparam unsigned READ_BURST_MAX = 256)
   (input wire                         ACLK,
    input wire 			       ARESETn,
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
    input wire 			       ARREADY);

   // Import the properties in this scope
   import amba_axi4_definition_of_axi4_lite::*;
   import amba_axi4_single_interface_requirements::*;
   import amba_axi4_transaction_structure::*;
   import amba_axi4_transaction_attributes::*;
   import amba_axi4_atomic_accesses::*;

   // Default clocking for all properties
   default clocking axi4_aclk @(posedge ACLK); endclocking

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                          Helper logic                           *
    *            ><><><><><><><><><><><><><><><><><><><><             */

   // Configure unsupported AXI4-Lite signals
   logic AR_unsupported_sig;
   assign AR_unsupported_sig = (/* The burst length is defined to be 1,
				 * equivalent to an AxLEN value of zero. */
				ARLEN    == 8'b00000000 &&
				/* All accesses are defined to be the width
				 * of the data bus. */
				ARSIZE   == BURST_SIZE_MAX &&
				/* The burst type has no meaning because the burst
				 * length is 1. */
				ARBURST  == 2'b00 &&
				/* All accesses are defined as Normal accesses,
				 * equivalent to an AxLOCK value of zero. */
				ARLOCK   == 1'b0 &&
				/* All accesses are defined as Non-modifiable,
				 * Non-bufferable, equivalent to an AxCACHE
				 * value of 0b0000. */
				ARCACHE  == 4'b0000 &&
				/* A default value of 0b0000 indicates that
				 * the interface is not participating in any
				 * QoS scheme. */
				ARQOS    == 4'b0000 &&
				/* Table A10-1 Master interface write channel
				 * signals and default signal values.
				 * AWREGION Default all zeros. */
				ARREGION == 4'b0000 &&
				/* Optional User-defined signal in the write address channel.
				 * Supported only in AXI4. */
				ARUSER   == {cfg.ARUSER_WIDTH{1'b0}} &&
	                        /* AXI4-Lite does not support AXI IDs. This means
	                         * all transactions must be in order, and all
	                         * accesses use a single fixed ID value. */
	                        ARID     == {cfg.ID_WIDTH{1'b0}});

   /* Upper 4 bits are never set for AxLEN <= 16.
    * it can also be: let FIXED_len = ARLEN inside {[0:15]} */
   let AR_FIXED_len = ARLEN[7:4] == 4'b000;

   logic [cfg.ADDRESS_WIDTH-1:0] end_addr;
   logic ar_4KB_boundary;
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
	    end_addr = (ARADDR + (ARLEN << ARSIZE));
	    ar_4KB_boundary = ARADDR[cfg.ADDRESS_WIDTH-1:12] == end_addr[cfg.ADDRESS_WIDTH-1:12];
	 end
      end // if (cfg.ADDRESS_WIDTH > 12)
   endgenerate

   logic m_bit;
   logic ra_bit;
   logic wa_bit;

   always_comb begin
      // Modifiable bit (renamed from <cacheable> (AXI3)), see A4.3.1
      m_bit = ARCACHE[1];
      // Read-allocate bit
      ra_bit = ARCACHE[2];
      // Write-allocate bit
      wa_bit = ARCACHE[3];
   end

   typedef struct packed {
      /* A burst must not cross a
       * 4KB address boundary (pA3-46). */
      bit [11:0] raddr_total_bytes;
      /* The maximum number of bytes
       * that can be transferred in an
       * exclusive burst is 128. (pA7-97). */
      bit [11:0] raddr_mask_exclusive;
      /* Aligment is correct if LSB bits of
       * based on araddr & arlen & arsize are LOW. */
      bit raddr_exclusive_aligned;
   } raddr_exclusive_alignment_dbg;
   raddr_exclusive_alignment_dbg raddr_excl_align;
   bit ar_excl_align;

   always_comb begin
      // Get the total bytes of the transaction
      raddr_excl_align.raddr_total_bytes = ((ARLEN + 1'b1) << ARSIZE);
      // Now calculate the mask, that is, remove the 1 appended to ARLEN (for debugging purposes)
      raddr_excl_align.raddr_mask_exclusive = raddr_excl_align.raddr_total_bytes - 1'b1;
      // Check that LSB bits are LOW
      raddr_excl_align.raddr_exclusive_aligned = ((raddr_excl_align.raddr_mask_exclusive &
						   ARADDR[10:0]) == 1'b0);
      ar_excl_align = raddr_excl_align.raddr_exclusive_aligned;
   end

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *            Section B1.1: Definition of AXI4-Lite                *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.PROTOCOL_TYPE == AXI4LITE) begin: axi4lite_defs
         // Configure the AXI4-Lite checker unsupported signals.
	 cp_AR_unsupported_axi4l: assume property(disable iff (!ARESETn) axi4_lite_unsupported_sig(AR_unsupported_sig))
	   else $error("Violation: For AR in AXI4-Lite, only signals described in B1.1 are",
		       "required or supported (B1.1 Definition of AXI4-Lite, pB1-126).");
	 // Guard correct AXI4-Lite DATA_WIDTH since the parameter is used here.
         if(cfg.CHECK_PARAMETERS == 1) begin: check_dataw
            ap_AR_AXI4LITE_DATAWIDTH: assert property(axi4l_databus_width(cfg.DATA_WIDTH))
              else $error("Violation: AXI4-Lite supports a data bus width of 32-bit or 64-bit",
                          "(B.1 Definition of AXI4-Lite, pB1-126).");
         end
      end
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                              ARID                               *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
         if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
            ap_AR_STABLE_AWID: assert property(disable iff(!ARESETn) stable_before_handshake(ARVALID, ARREADY, ARID))
              else $error("Violation: Once the master has asserted ARVALID, data and control information",
                          "from master must remain stable [ARID] until ARREADY is asserted",
                          "(A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
               ap_AR_ARID_X: assert property(disable iff(!ARESETn) valid_information(ARVALID, ARID))
                 else $error("Violation : The source can assert the [AR]VALID signal only when it",
                             "drives valid address and control information (A3.2.2 Channel signaling",
                             "requirements pA3-40).");
            end
         end
         else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
            cp_AR_STABLE_ARID: assume property(disable iff(!ARESETn) stable_before_handshake(ARVALID, ARREADY, ARID))
              else $error("Violation: Once the master has asserted ARVALID, data and control information",
                          "from master must remain stable [ARID] until ARREADY is asserted",
                          "(A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
               cp_AR_ARID_X: assume property(disable iff(!ARESETn) valid_information(ARVALID, ARID))
                 else $error("Violation : The source can assert the [AR]VALID signal only when it",
                             "drives valid address and control information (A3.2.2 Channel signaling",
                             "requirements pA3-40).");
            end
         end
      end // if (cfg.PROTOCOL_TYPE == AXI4FULL)
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                              ARADDR                             *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	 ap_AR_STABLE_ARADDR: assert property(disable iff(!ARESETn) stable_before_handshake(ARVALID, ARREADY, ARADDR))
           else $error("Violation: Once the master has asserted ARVALID, data and control information",
                       "from master must remain stable [ARADDR] until ARREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 if(cfg.ENABLE_XPROP) begin
            ap_AR_ARADDR_X: assert property(disable iff(!ARESETn) valid_information(ARVALID, ARADDR))
              else $error("Violation : The source can assert the [AR]VALID signal only when it",
                          "drives valid address and control information (A3.2.2 Channel signaling",
                          "requirements pA3-40).");
         end
      end
      else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
	 cp_AR_STABLE_ARADDR: assume property(disable iff(!ARESETn) stable_before_handshake(ARVALID, ARREADY, ARADDR))
           else $error("Violation: Once the master has asserted ARVALID, data and control information",
                       "from master must remain stable [ARADDR] until ARREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 if(cfg.ENABLE_XPROP) begin
            cp_AR_ARADDR_X: assume property(disable iff(!ARESETn) valid_information(ARVALID, ARADDR))
              else $error("Violation : The source can assert the [AR]VALID signal only when it",
                          "drives valid address and control information (A3.2.2 Channel signaling",
                          "requirements pA3-40).");
         end
      end
      if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
	 if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	    if(cfg.ADDRESS_WIDTH > 12) begin
	       ap_AR_ARADDR_BOUNDARY_4KB: assert property(disable iff(!ARESETn) burst_cache_line_boundary(ARVALID, ARBURST, ar_4KB_boundary))
		 else $error("Violation: A write burst must not cross a 4KB address boundary (A3.4.1 Address structure, pA3-46).");
	    end
	    if(BURST_SIZE_MAX >= 1) begin
	       ap_AR_ADDRESS_ALIGMENT: assert property(disable iff(!ARESETn) start_address_align(ARVALID, ARBURST, ARADDR[6:0], ARSIZE))
		 else $error("Violation: The start address must be aligned to the size of each transfer",
			     "(A3.4.1 Address structure, pA3-48).");
	    end
	    if(cfg.EXCLUSIVE_ACCESS == 1) begin
	       ap_AR_ADDRESS_ALIGNMENT_EXCLUSIVE: assert property(disable iff(!ARESETn) exclusive_access_addr_align(ARVALID, ARLEN, ARLOCK, ar_excl_align))
		 else $error("Violation: The address of an exclusive access must be aligned to the total number of bytes in the transaction",
			     "(A7.2.4 Exclusive access restrictions, pA7-97.)");
	    end
	 end
	 else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
	    if(cfg.ADDRESS_WIDTH > 12) begin
	       cp_AR_ARADDR_BOUNDARY_4KB: assume property(disable iff(!ARESETn) burst_cache_line_boundary(ARVALID, ARBURST, ar_4KB_boundary))
		 else $error("Violation: A write burst must not cross a 4KB address boundary (A3.4.1 Address structure, pA3-46).");
	    end
	    if(BURST_SIZE_MAX >= 1) begin
	       cp_AR_address_alignment: assume property(disable iff(!ARESETn) start_address_align(ARVALID, ARBURST, ARADDR[6:0], ARSIZE))
		 else $error("Violation: The start address must be aligned to the size of each transfer",
			     "(A3.4.1 Address structure, pA3-48).");
	    end
	    if(cfg.EXCLUSIVE_ACCESS == 1) begin
	       cp_AR_ADDRESS_ALIGNMENT_EXCLUSIVE: assume property(disable iff(!ARESETn) exclusive_access_addr_align(ARVALID, ARLEN, ARLOCK, ar_excl_align))
		 else $error("Violation: The address of an exclusive access must be aligned to the total number of bytes in the transaction",
			     "(A7.2.4 Exclusive access restrictions, pA7-97.)");
	    end
	 end
      end // if (cfg.PROTOCOL_TYPE == AXI4FULL)
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                              ARLEN                              *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
      if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	 if(cfg.CHECK_PARAMETERS) begin
	    ap_AR_ARLEN_MAX: assert property(ARLEN < READ_BURST_MAX)
              else $error("Violation: Parameter WRITE_BURST_MAX determines the max burst lenght capability of",
			  "the DUT, and cannot issue a transaction of ARLEN > READ_BURST_MAX.");
	    ap_AR_ARLEN_MAX_RD_BURST_LEN: assert property(ARVALID |-> ARLEN < cfg.MAX_RD_LENGTH)
	      else $error("Violation: Parameter MAX_RD_LENGTH determines the exact number of transfers in a",
			  "burst. The DUT should honor this setting or the user must increase the value of it.");
	 end
         ap_AR_STABLE_ARLEN: assert property(disable iff(!ARESETn) stable_before_handshake(ARVALID, ARREADY, ARLEN))
           else $error("Violation: Once the master has asserted ARVALID, data and control information",
                       "from master must remain stable [ARLEN] until ARREADY is asserted",
                       "(A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 if(cfg.ENABLE_XPROP) begin
            ap_AR_ARLEN_X: assert property(disable iff(!ARESETn) valid_information(ARVALID, ARLEN))
              else $error("Violation : The source can assert the [AR]VALID signal only when it",
                          "drives valid address and control information (A3.2.2 Channel signaling",
                          "requirements pA3-40).");
         end
	 ap_AR_VALID_WRAP_BURST: assert property(disable iff(!ARESETn) valid_wrap_burst_length(ARVALID, ARBURST, ARLEN))
           else $error("Violation: For wrapping bursts, the burst length must be 2, 4, 8 or 16 (A3.4.1 Address structure, pA3-46).");
	 ap_AR_VALID_LEN_FIXED: assert property(disable iff(!ARESETn) supported_burst_transfer(ARVALID, ARBURST, FIXED, AR_FIXED_len))
           else $error("Violation: Support for FIXED burst type in AXI4 remains at 1 to 16 transfers (A3.4.1 Address structure, pA3-46).");
	 ap_AR_EXCLUSIVE_BYTES_TRANSFER: assert property(disable iff(!ARESETn) valid_number_bytes_exclusive(ARVALID, ARLOCK, ARLEN))
	   else $error("Violation: The number of bytes to be transferred in an exclusive access burst must be a power of 2,",
		       "that is, 1, 2, 4, 8, 16, 32, 64, or 128 bytes. (A7.2.4 Exclusive access restrictions, pA7-97).");
      end
      else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
	 if(cfg.CHECK_PARAMETERS) begin
	    cp_AR_ARLEN_MAX: assume property(ARLEN < READ_BURST_MAX)
              else $error("Violation: Parameter WRITE_BURST_MAX determines the max burst lenght capability of",
			  "the DUT, and cannot issue a transaction of ARLEN > READ_BURST_MAX.");
	    cp_AR_ARLEN_MAX_RD_BURST_LEN: assume property(ARVALID |-> ARLEN < cfg.MAX_RD_LENGTH)
	      else $error("Violation: Parameter MAX_RD_LENGTH determines the exact number of transfers in a",
			  "burst. The DUT should honor this setting or the user must increase the value of it.");
	 end
         cp_AR_STABLE_ARLEN: assume property(disable iff(!ARESETn) stable_before_handshake(ARVALID, ARREADY, ARLEN))
           else $error("Violation: Once the master has asserted ARVALID, data and control information",
                       "from master must remain stable [ARLEN] until ARREADY is asserted",
                       "(A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 if(cfg.ENABLE_XPROP) begin
            cp_AR_ARLEN_X: assume property(disable iff(!ARESETn) valid_information(ARVALID, ARLEN))
              else $error("Violation : The source can assert the [AR]VALID signal only when it",
                          "drives valid address and control information (A3.2.2 Channel signaling",
                          "requirements pA3-40).");
         end
	 cp_AR_VALID_WRAP_BURST: assume property(disable iff(!ARESETn) valid_wrap_burst_length(ARVALID, ARBURST, ARLEN))
           else $error("Violation: For wrapping bursts, the burst length must be 2, 4, 8 or 16 (A3.4.1 Address structure, pA3-46).");
	 cp_AR_VALID_LEN_FIXED: assume property(disable iff(!ARESETn) supported_burst_transfer(ARVALID, ARBURST, FIXED, AR_FIXED_len))
           else $error("Violation: Support for FIXED burst type in AXI4 remains at 1 to 16 transfers (A3.4.1 Address structure, pA3-46).");
	 cp_AR_EXCLUSIVE_BYTES_TRANSFER: assume property(disable iff(!ARESETn) valid_number_bytes_exclusive(ARVALID, ARLOCK, ARLEN))
	   else $error("Violation: The number of bytes to be transferred in an exclusive access burst must be a power of 2,",
		       "that is, 1, 2, 4, 8, 16, 32, 64, or 128 bytes. (A7.2.4 Exclusive access restrictions, pA7-97).");
      end
   end // if (cfg.PROTOCOL_TYPE == AXI4FULL)

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                              ARSIZE                             *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
	 if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	    ap_AR_STABLE_ARSIZE: assert property(disable iff(!ARESETn) stable_before_handshake(ARVALID, ARREADY, ARSIZE))
              else $error("Violation: Once the master has asserted ARVALID, data and control information",
			  "from master must remain stable [ARSIZE] until ARREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
               ap_AR_ARSIZE_X: assert property(disable iff(!ARESETn) valid_information(ARVALID, ARSIZE))
		 else $error("Violation : The source can assert the [AR]VALID signal only when it",
                             "drives valid address and control information (A3.2.2 Channel signaling",
                             "requirements pA3-40).");
            end
	    ap_AR_CORRECT_BURST_SIZE: assert property(disable iff(!ARESETn) burst_size_within_width_boundary(ARVALID, ARSIZE, STRB_WIDTH))
              else $error("Violation: The size of any transfer must not exceed the data bus width of either agent in the transaction.",
                          "(A3.4.1 Address structure, Burst size, pA3-47.");
	 end
	 else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
            cp_AR_STABLE_ARSIZE: assume property(disable iff(!ARESETn) stable_before_handshake(ARVALID, ARREADY, ARSIZE))
              else $error("Violation: Once the master has asserted ARVALID, data and control information",
			  "from master must remain stable [ARSIZE] until ARREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
               cp_AR_ARSIZE_X: assume property(disable iff(!ARESETn) valid_information(ARVALID, ARSIZE))
		 else $error("Violation : The source can assert the [AR]VALID signal only when it",
                             "drives valid address and control information (A3.2.2 Channel signaling",
                             "requirements pA3-40).");
            end
	    cp_AR_CORRECT_BURST_SIZE: assume property(disable iff(!ARESETn) burst_size_within_width_boundary(ARVALID, ARSIZE, STRB_WIDTH))
              else $error("Violation: The size of any transfer must not exceed the data bus width of either agent in the transaction.",
                          "(A3.4.1 Address structure, Burst size, pA3-47.");
	 end
      end // if (cfg.PROTOCOL_TYPE == AXI4FULL)
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                              ARBURST                            *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
	 if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	    ap_AR_STABLE_ARBURST: assert property(disable iff(!ARESETn) stable_before_handshake(ARVALID, ARREADY, ARBURST))
              else $error("Violation: Once the master has asserted ARVALID, data and control information",
			  "from master must remain stable [ARBURST] until ARREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
               ap_AR_ARBURST_X: assert property(disable iff(!ARESETn) valid_information(ARVALID, ARBURST))
		 else $error("Violation : The source can assert the [AR]VALID signal only when it",
                             "drives valid address and control information (A3.2.2 Channel signaling",
                             "requirements pA3-40).");
            end
	    ap_AR_BURST_TYPES: assert property(disable iff(!ARESETn) ARVALID |-> ARBURST != RESERVED)
	      else $error("Violation: The AXI protocol defines three burst types, FIXED, INCR and WRAP. RESERVED is undefined",
			  "and therefore not a valid burst (A3.4.1 Address structure, pA3-48, Table A3-3 Burst type encoding).");
	 end
	 else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
            cp_AR_STABLE_ARBURST: assume property(disable iff(!ARESETn) stable_before_handshake(ARVALID, ARREADY, ARBURST))
              else $error("Violation: Once the master has asserted ARVALID, data and control information",
			  "from master must remain stable [ARBURST] until ARREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
               cp_AR_ARBURST_X: assume property(disable iff(!ARESETn) valid_information(ARVALID, ARBURST))
		 else $error("Violation : The source can assert the [AR]VALID signal only when it",
                             "drives valid address and control information (A3.2.2 Channel signaling",
                             "requirements pA3-40).");
            end
	    cp_AR_BURST_TYPES: assume property(disable iff(!ARESETn) ARVALID |-> ARBURST != RESERVED)
	      else $error("Violation: The AXI protocol defines three burst types, FIXED, INCR and WRAP. RESERVED is undefined",
			  "and therefore not a valid burst (A3.4.1 Address structure, pA3-48, Table A3-3 Burst type encoding).");
	 end
      end // if (cfg.PROTOCOL_TYPE == AXI4FULL)
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                              ARLOCK                             *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
	 if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	    ap_AR_STABLE_ARLOCK: assert property(disable iff(!ARESETn) stable_before_handshake(ARVALID, ARREADY, ARLOCK))
              else $error("Violation: Once the master has asserted ARVALID, data and control information",
			  "from master must remain stable [ARLOCK] until ARREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
               ap_AR_ARLOCK_X: assert property(disable iff(!ARESETn) valid_information(ARVALID, ARLOCK))
		 else $error("Violation : The source can assert the [AR]VALID signal only when it",
                             "drives valid address and control information (A3.2.2 Channel signaling",
                             "requirements pA3-40).");
            end
	    ap_AR_BURST_LEN_EXCLUSIVE: assert property(disable iff(!ARESETn) valid_burst_len_exclusive(ARVALID, ARLOCK, ARLEN))
	      else $error("Violation: In AXI4, the burst length for an exclusive access must not exceed 16 transfers",
			  "(Ref: A7.2.4 Exclusive access restrictions, pA7-97).");
	 end
	 else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
            cp_AR_STABLE_ARLOCK: assume property(disable iff(!ARESETn) stable_before_handshake(ARVALID, ARREADY, ARLOCK))
              else $error("Violation: Once the master has asserted ARVALID, data and control information",
			  "from master must remain stable [ARLOCK] until ARREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
               cp_AR_ARLOCK_X: assume property(disable iff(!ARESETn) valid_information(ARVALID, ARLOCK))
		 else $error("Violation : The source can assert the [AR]VALID signal only when it",
                             "drives valid address and control information (A3.2.2 Channel signaling",
                             "requirements pA3-40).");
            end
	    cp_AR_BURST_LEN_EXCLUSIVE: assume property(disable iff(!ARESETn) valid_burst_len_exclusive(ARVALID, ARLOCK, ARLEN))
	      else $error("Violation: In AXI4, the burst length for an exclusive access must not exceed 16 transfers",
			  "(Ref: A7.2.4 Exclusive access restrictions, pA7-97).");
	 end
      end // if (cfg.PROTOCOL_TYPE == AXI4FULL)
      if(cfg.PROTOCOL_TYPE == AXI4LITE) begin
	 if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	    ap_AR_UNSUPPORTED_EXCLUSIVE: assert property(disable iff (!ARESETn) unsupported_exclusive_access(ARVALID, ARLOCK, EXCLUSIVE))
              else $error("Violation: Exclusive read accesses are not supported in AXI4 Lite",
			  "(Definition of AXI4-Lite, pB1-126).");
	 end
	 else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
	    cp_AR_UNSUPPORTED_EXCLUSIVE: assume property(disable iff (!ARESETn) unsupported_exclusive_access(ARVALID, ARLOCK, EXCLUSIVE))
              else $error("Violation: Exclusive read accesses are not supported in AXI4 Lite",
			  "(Definition of AXI4-Lite, pB1-126).");
	 end
      end
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                              ARCACHE                            *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
	 if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	    ap_AR_STABLE_ARCACHE: assert property(disable iff(!ARESETn) stable_before_handshake(ARVALID, ARREADY, ARCACHE))
              else $error("Violation: Once the master has asserted ARVALID, data and control information",
			  "from master must remain stable [ARCACHE] until ARREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
               ap_AR_ARCACHE_X: assert property(disable iff(!ARESETn) valid_information(ARVALID, ARCACHE))
		 else $error("Violation : The source can assert the [AR]VALID signal only when it",
                             "drives valid address and control information (A3.2.2 Channel signaling",
                             "requirements pA3-40).");
            end
	    ap_AR_MEMORY_TYPE_ENCODING: assert property(disable iff(!ARESETn) memory_type_encoding(ARVALID, ARCACHE))
	      else $error("Violation: For memory types, all values not shown in Table A4-5 are reserved,",
			  "(A4.4 Memory types, pA4-67, Table A4-5 Memory type encoding");
	    ap_AR_NON_CACHEABLE: assert property(ARVALID && ARLOCK |-> {ra_bit, wa_bit} == 2'b00)
              else $error("Violation: When Modifiable bit is not asserted, Read-allocate and Write-allocate bits",
                          "cannot indicate a cacheable transaction (A4.4 Memory types, Table A4-5 Memory type encoding, pA4-67).");
	 end
	 else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
            cp_AR_STABLE_ARCACHE: assume property(disable iff(!ARESETn) stable_before_handshake(ARVALID, ARREADY, ARCACHE))
              else $error("Violation: Once the master has asserted ARVALID, data and control information",
			  "from master must remain stable [ARCACHE] until ARREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
               cp_AR_ARCACHE_X: assume property(disable iff(!ARESETn) valid_information(ARVALID, ARCACHE))
		 else $error("Violation : The source can assert the [AR]VALID signal only when it",
                             "drives valid address and control information (A3.2.2 Channel signaling",
                             "requirements pA3-40).");
            end
	    cp_AR_MEMORY_TYPE_ENCODING: assume property(disable iff(!ARESETn) memory_type_encoding(ARVALID, ARCACHE))
	      else $error("Violation: For memory types, all values not shown in Table A4-5 are reserved,",
			  "(A4.4 Memory types, pA4-67, Table A4-5 Memory type encoding");
	    cp_AR_NON_CACHEABLE: assume property(ARVALID && ARLOCK |-> {ra_bit, wa_bit} == 2'b00)
              else $error("Violation: When Modifiable bit is not asserted, Read-allocate and Write-allocate bits",
                          "cannot indicate a cacheable transaction (A4.4 Memory types, Table A4-5 Memory type encoding, pA4-67).");
	 end
      end // if (cfg.PROTOCOL_TYPE == AXI4FULL)
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                              ARPROT                             *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	 ap_AR_STABLE_ARPROT: assert property(disable iff(!ARESETn) stable_before_handshake(ARVALID, ARREADY, ARPROT))
           else $error("Violation: Once the master has asserted ARVALID, data and control information",
		       "from master must remain stable [ARPROT] until ARREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 if(cfg.ENABLE_XPROP) begin
            ap_AR_ARPROT_X: assert property(disable iff(!ARESETn) valid_information(ARVALID, ARPROT))
	      else $error("Violation : The source can assert the [AR]VALID signal only when it",
                          "drives valid address and control information (A3.2.2 Channel signaling",
                          "requirements pA3-40).");
	 end
      end
      else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
         cp_AR_STABLE_ARPROT: assume property(disable iff(!ARESETn) stable_before_handshake(ARVALID, ARREADY, ARPROT))
           else $error("Violation: Once the master has asserted ARVALID, data and control information",
		       "from master must remain stable [ARPROT] until ARREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 if(cfg.ENABLE_XPROP) begin
	    cp_AR_ARPROT_X: assume property(disable iff(!ARESETn) valid_information(ARVALID, ARPROT))
	      else $error("Violation : The source can assert the [AR]VALID signal only when it",
                          "drives valid address and control information (A3.2.2 Channel signaling",
                          "requirements pA3-40).");
         end
      end
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                              ARQOS                              *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
	 if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	    ap_AR_STABLE_ARQOS: assert property(disable iff(!ARESETn) stable_before_handshake(ARVALID, ARREADY, ARQOS))
              else $error("Violation: Once the master has asserted ARVALID, data and control information",
			  "from master must remain stable [ARQOS] until ARREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
               ap_AR_ARQOS_X: assert property(disable iff(!ARESETn) valid_information(ARVALID, ARQOS))
		 else $error("Violation : The source can assert the [AR]VALID signal only when it",
                             "drives valid address and control information (A3.2.2 Channel signaling",
                             "requirements pA3-40).");
	    end
	 end
	 else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
            cp_AR_STABLE_ARQOS: assume property(disable iff(!ARESETn) stable_before_handshake(ARVALID, ARREADY, ARQOS))
              else $error("Violation: Once the master has asserted ARVALID, data and control information",
			  "from master must remain stable [ARQOS] until ARREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
               cp_AR_ARQOS_X: assume property(disable iff(!ARESETn) valid_information(ARVALID, ARQOS))
		 else $error("Violation : The source can assert the [AR]VALID signal only when it",
                             "drives valid address and control information (A3.2.2 Channel signaling",
                             "requirements pA3-40).");
	    end
	 end
      end // if (cfg.PROTOCOL_TYPE == AXI4FULL)
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                            ARREGION                             *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
	 if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	    ap_AR_STABLE_ARREGION: assert property(disable iff(!ARESETn) stable_before_handshake(ARVALID, ARREADY, ARREGION))
              else $error("Violation: Once the master has asserted ARVALID, data and control information",
			  "from master must remain stable [ARREGION] until ARREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
               ap_AR_ARREGION_X: assert property(disable iff(!ARESETn) valid_information(ARVALID, ARREGION))
		 else $error("Violation : The source can assert the [AR]VALID signal only when it",
                             "drives valid address and control information (A3.2.2 Channel signaling",
                             "requirements pA3-40).");
	    end
	 end
	 else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
            cp_AR_STABLE_ARREGION: assume property(disable iff(!ARESETn) stable_before_handshake(ARVALID, ARREADY, ARREGION))
              else $error("Violation: Once the master has asserted ARVALID, data and control information",
			  "from master must remain stable [ARREGION] until ARREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
               cp_AR_ARREGION_X: assume property(disable iff(!ARESETn) valid_information(ARVALID, ARREGION))
		 else $error("Violation : The source can assert the [AR]VALID signal only when it",
                             "drives valid address and control information (A3.2.2 Channel signaling",
                             "requirements pA3-40).");
	    end
	 end
      end // if (cfg.PROTOCOL_TYPE == AXI4FULL)
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                              ARUSER                             *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
	 if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	    ap_AR_STABLE_ARUSER: assert property(disable iff(!ARESETn) stable_before_handshake(ARVALID, ARREADY, ARUSER))
              else $error("Violation: Once the master has asserted ARVALID, data and control information",
			  "from master must remain stable [ARUSER] until ARREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
               ap_AR_ARUSER_X: assert property(disable iff(!ARESETn) valid_information(ARVALID, ARUSER))
		 else $error("Violation : The source can assert the [AR]VALID signal only when it",
                             "drives valid address and control information (A3.2.2 Channel signaling",
                             "requirements pA3-40).");
	    end
	 end
	 else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
            cp_AR_STABLE_ARUSER: assume property(disable iff(!ARESETn) stable_before_handshake(ARVALID, ARREADY, ARUSER))
              else $error("Violation: Once the master has asserted ARVALID, data and control information",
			  "from master must remain stable [ARUSER] until ARREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
               cp_AR_ARUSER_X: assume property(disable iff(!ARESETn) valid_information(ARVALID, ARUSER))
		 else $error("Violation : The source can assert the [AR]VALID signal only when it",
                             "drives valid address and control information (A3.2.2 Channel signaling",
                             "requirements pA3-40).");
	    end
	 end
      end // if (cfg.PROTOCOL_TYPE == AXI4FULL)
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                              ARVALID                            *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.OPTIONAL_RESET == 1) begin
	 if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
            ap_AR_EXIT_RESET: assert property(exit_from_reset(ARESETn, ARVALID))
	      else $error("Violation: ARVALID must be low for the first clock edge",
                          "after ARESETn goes high (A3.2.1 Reset, pA3-38, Figure A3-1).");
	 end
         else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
            cp_AR_EXIT_RESET: assume property(exit_from_reset(ARESETn, ARVALID))
	      else $error("Violation: ARVALID must be low for the first clock edge",
                          "after ARESETn goes high (A3.2.1 Reset, pA3-38, Figure A3-1).");
	 end
      end // if (cfg.OPTIONAL_RESET == 1)
      if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	 ap_AR_ARVALID_until_ARREADY: assert property(disable iff (!ARESETn) valid_before_handshake(ARVALID, ARREADY))
	   else $error("Violation: Once ARVALID is asserted it must remain asserted until the handshake",
		       "occurs  (A3.2.1 Handshake process, pA3-39).");
	 if(cfg.ENABLE_XPROP) begin
            ap_AR_ARVALID_X: assume property(disable iff(!ARESETn) valid_information(ARESETn, ARVALID))
	      else $error("Violation : The source can assert the [AR]VALID signal only when it",
                          "drives valid address and control information (A3.2.2 Channel signaling",
                          "requirements pA3-40).");
	 end
      end
      else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
	 cp_AR_ARVALID_until_ARREADY: assume property(disable iff (!ARESETn) valid_before_handshake(ARVALID, ARREADY))
	   else $error("Violation: Once ARVALID is asserted it must remain asserted until the handshake",
		       "occurs  (A3.2.1 Handshake process, pA3-39).");
	 if(cfg.ENABLE_XPROP) begin
	    cp_AR_ARVALID_X: assume property(disable iff(!ARESETn) valid_information(ARESETn, ARVALID))
	      else $error("Violation : The source can assert the [AR]VALID signal only when it",
                          "drives valid address and control information (A3.2.2 Channel signaling",
                          "requirements pA3-40).");
	 end
      end
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                             ARREADY                             *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, MONITOR}) begin
         if(cfg.ENABLE_XPROP) begin
            ap_AR_ARREADY_X: assert property(disable iff(!ARESETn) valid_information(ARESETn, ARREADY))
              else $error("Violation : The source can assert the [AR]VALID signal only when it",
                          "drives valid address and control information (A3.2.2 Channel signaling",
                          "requirements pA3-40).");
         end
      end
      else if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, CONSTRAINT}) begin
         if(cfg.ENABLE_XPROP) begin
            cp_AR_ARREADY_X: assume property(disable iff(!ARESETn) valid_information(ARESETn, ARREADY))
              else $error("Violation : The source can assert the [AR]VALID signal only when it",
                          "drives valid address and control information (A3.2.2 Channel signaling",
                          "requirements pA3-40).");
         end
      end
   endgenerate


   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                        AMBA Recommended                         *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.ARM_RECOMMENDED == 1) begin
         if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, MONITOR}) begin
            ap_AR_READY_MAXWAIT: assert property(disable iff(!ARESETn) handshake_max_wait(ARVALID, ARREADY, cfg.MAXWAIT))
              else $error("Violation: ARREADY should be asserted within MAXWAIT cycles of ARVALID being asserted (AMBA recommended).");
         end
         else if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, CONSTRAINT}) begin
            cp_AR_READY_MAXWAIT: assume property(disable iff(!ARESETn) handshake_max_wait(ARVALID, ARREADY, cfg.MAXWAIT))
              else $error("Violation: ARREADY should be asserted within MAXWAIT cycles of ARVALID being asserted (AMBA recommended).");
         end
      end
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *              Covers To Maximise Debug Information               *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   let handshake_with_burst_type(burst_type) = (ARVALID && ARREADY && (ARBURST == burst_type));
   let handshake_with_lock_type(lock_type) = (ARVALID && ARREADY && (ARLOCK == lock_type));
   let protection_encoding(axprot, value) = (ARVALID && ARREADY && (axprot == value));
   let AR_request_accepted = ARVALID && ARREADY;

   generate
      // Witnessing scenarios stated in the AMBA AXI4 spec
      if (cfg.ENABLE_COVER == 1) begin: witness
	 // Single handshake
         sequence ar_handshake_cond(cond);
            ARVALID ##0 ARREADY ##0 cond;
         endsequence // aw_burst_size

         /* This sequence looks for two handshakes
          * and is used to witness a transaction
          * process where two request are made
          * with different ID. */
         sequence ar_two_handshakes;
            ARVALID ##0 ARREADY ##1
            ARVALID ##0 ARREADY;
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
            ARVALID ##0 ARREADY ##0 ARBURST == WRAP
            ##0 ARLEN == l;
         endsequence // wrapping_burst_len

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
            ARVALID ##0 ARREADY ##0 ARSIZE == SIZE2B
            ##0 ARADDR[a] == 1'b1 ##0 ARBURST == t;
         endsequence // unaligned_transfer


	 /*            ><><><><><><><><><><><><><><><><><><><><             *
	  *                              ARID                               *
	  *            ><><><><><><><><><><><><><><><><><><><><             */
	 if(cfg.VERIFY_AGENT_TYPE != DESTINATION) begin
            if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
               wp_TWO_TRANSACTIONS_DIFFERENT_ARID: cover property(ar_two_handshakes ##0 ARID != $past(ARID))
                 $info("Witnessed: Two transactions tagged with different ID.");
               for(genvar idx = 0; idx < (2**cfg.ID_WIDTH); idx++) begin
                  wp_ARID_TAG_NUMBER: cover property(ar_handshake_cond(ARID == idx))
                    $info("Witnessed: Transaction ID covering all possible values derived by ID_WIDTH parameter.");
               end
            end
         end

	 /*            ><><><><><><><><><><><><><><><><><><><><             *
	  *                              ARADDR                             *
	  *            ><><><><><><><><><><><><><><><><><><><><             */
	 if(cfg.VERIFY_AGENT_TYPE != DESTINATION) begin
            if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
               wp_UNALIGNED_TRANSFERS_FIXED_BURST: cover property(unaligned_transfer(0, FIXED))
                 $info("Witnessed: Source signaling an unaligned transfer with burst type FIXED (pA3-54).");
               wp_UNALIGNED_TRANSFERS_INCR_BURST: cover property(unaligned_transfer(1, INCR))
                 $info("Witnessed: Source signaling an unaligned transfer with burst type INCR (pA3-54).");
            end
         end

	 /*              ><><><><><><><><><><><><><><><><><><><><             *
          *                                ARLEN                              *
          *              ><><><><><><><><><><><><><><><><><><><><             */
         if(cfg.VERIFY_AGENT_TYPE != DESTINATION) begin
            if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
               for(genvar i = 0; i < $clog2(cfg.MAX_RD_LENGTH); i++) begin: read_transaction_len
                  wp_AR_LEN_TRANSFERS: cover property(AR_request_accepted && ARLEN == i)
                  $info("Witnessed: Burst lenght of size 0 to MAX_RD_LENGTH",
                        "(A3.4.1 Address strucutre, pA3-46).");
               end
               /* TODO: Bring here outstanding transaction counters to create covers for
                * first transactions with different ARLEN values. */
               for(genvar len = 2; len <= cfg.MAX_RD_LENGTH; len = len * 2) begin
                  wp_WRAPPING_BURST_LEN: cover property(wrapping_burst_len((len -  1'b1)))
                    $info("Witnessed: Wrapping burst len of 2, 4, 8 and 16 transfers");
               end
            end // if (cfg.PROTOCOL_TYPE == AXI4FULL)
         end // if (cfg.VERIFY_AGENT_TYPE != DESTINATION)


         wp_ARVALID_before_ARREADY: cover property (disable iff (!ARESETn) valid_before_ready(ARVALID, ARREADY))
           $info("Witnessed: Handshake process pA3-39, Figure A3-2 VALID before READY handshake capability.");
         wp_ARREADY_before_ARVALID: cover property (disable iff (!ARESETn) ready_before_valid(ARVALID, ARREADY))
           $info("Witnessed: Handshake process pA3-39, Figure A3-3 READY before VALID handshake capability.");
         wp_ARVALID_with_ARREADY: cover property (disable iff (!ARESETn) valid_with_ready(ARVALID, ARREADY))
           $info("Witnessed: Handshake process pA3-39, Figure A3-4 VALID with READY handshake capability.");
	 if(cfg.PROTOCOL_TYPE == AXI4FULL && cfg.VERIFY_AGENT_TYPE != DESTINATION) begin
	    for(genvar i = 0; i <= cfg.MAX_RD_LENGTH-1; i++) begin: read_transaction_len
	       wp_AW_len_transfers: cover property(AR_request_accepted && ARLEN == i[7:0])
	       $info("Witnessed: Wrapping burst len of cfg.MAX_RD_LENGTH transfers.");
	    end
	 end
	 if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
	    wp_AR_BURST_FIXED: cover property(disable iff(!ARESETn) handshake_with_burst_type(FIXED))
	      $info("Witnessed: Burst type encoding FIXED as defined in Table A3-3 Burst type encoding, pA3-48.");
	    wp_AR_BURST_INCR: cover property(disable iff(!ARESETn) handshake_with_burst_type(INCR))
	      $info("Witnessed: Burst type encoding INCR as defined in Table A3-3 Burst type encoding, pA3-48.");
	    wp_AR_BURST_WRAP: cover property(disable iff(!ARESETn) handshake_with_burst_type(WRAP))
	      $info("Witnessed: Burst type encoding WRAP as defined in Table A3-3 Burst type encoding, pA3-48.");

	    wp_AR_ARLOCK_NORMAL: cover property(disable iff(!ARESETn) handshake_with_lock_type(NORMAL))
	      $info("Witnessed: Lock access type NORMAL as defined in Table A7-2 AXI4 atomic access encoding, pA7-100.");
	    wp_AR_ARLOCK_EXCLUSIVE: cover property(disable iff(!ARESETn) handshake_with_lock_type(EXCLUSIVE))
	      $info("Witnessed: Lock access type EXCLUSIVE as defined in Table A7-2 AXI4 atomic access encoding, pA7-100.");

	    if(cfg.VERIFY_AGENT_TYPE != DESTINATION) begin
	       wp_AR_ARPROT_UNPRIVILEGED: cover property(disable iff(!ARESETn) protection_encoding(ARPROT[0], 1'b0))
		 $info("Witnessed: ARPROT defining unprivileged access permission as defined in Table A4-6 Protection encoding",
		       "(A4.7 Access permissions, pA4-73).");
	       wp_AR_ARPROT_PRIVILEGED: cover property(disable iff(!ARESETn) protection_encoding(ARPROT[0], 1'b1))
		 $info("Witnessed: ARPROT defining privileged access permission as defined in Table A4-6 Protection encoding",
		       "(A4.7 Access permissions, pA4-73).");
	       wp_AR_ARPROT_SECURE: cover property(disable iff(!ARESETn) protection_encoding(ARPROT[1], 1'b0))
		 $info("Witnessed: ARPROT defining secure access permission as defined in Table A4-6 Protection encoding",
		       "(A4.7 Access permissions, pA4-73).");
	       wp_AR_ARPROT_NONSECURE: cover property(disable iff(!ARESETn) protection_encoding(ARPROT[1], 1'b1))
		 $info("Witnessed: ARPROT defining non-secure access permission as defined in Table A4-6 Protection encoding",
		       "(A4.7 Access permissions, pA4-73).");
	       wp_AR_ARPROT_DATA: cover property(disable iff(!ARESETn) protection_encoding(ARPROT[2], 1'b0))
		 $info("Witnessed: ARPROT defining data access permission as defined in Table A4-6 Protection encoding",
		       "(A4.7 Access permissions, pA4-73).");
	       wp_AR_ARPROT_INSTRUCTION: cover property(disable iff(!ARESETn) protection_encoding(ARPROT[2], 1'b1))
		 $info("Witnessed: ARPROT defining instruction access permission as defined in Table A4-6 Protection encoding",
		       "(A4.7 Access permissions, pA4-73).");
	    end // if (cfg.VERIFY_AGENT_TYPE != DESTINATION)
	 end // if (cfg.PROTOCOL_TYPE == AXI4FULL)
      end // block: witness
   endgenerate
endmodule // amba_axi4_read_address_channel
`default_nettype wire

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
module amba_axi4_write_data_channel
  import amba_axi4_protocol_checker_pkg::*;
   #(parameter axi4_checker_params_t cfg =
     '{DATA_WIDTH:        32,
       WUSER_WIDTH:       32,
       VERIFY_AGENT_TYPE: SOURCE,
       PROTOCOL_TYPE:     AXI4LITE,
       CHECK_PARAMETERS:  1,
       ENABLE_COVER:      1,
       ENABLE_XPROP:      1,
       ARM_RECOMMENDED:   1,
       MAXWAIT:           16,
       OPTIONAL_WSTRB:    1,
       OPTIONAL_RESET:    1,
       FULL_WR_STRB:      1,
       default:           0},
     localparam STRB_WIDTH = cfg.DATA_WIDTH/8)
   (input wire                       ACLK,
    input wire 			     ARESETn,
    input wire [cfg.DATA_WIDTH-1:0]  WDATA,
    input wire [STRB_WIDTH-1:0]      WSTRB,
    input wire 			     WLAST,
    input wire [cfg.WUSER_WIDTH-1:0] WUSER,
    input wire 			     WVALID,
    input wire 			     WREADY);

   // Import the properties in this scope
   import amba_axi4_definition_of_axi4_lite::*;
   import amba_axi4_single_interface_requirements::*;
   import amba_axi4_atomic_accesses::*;

   // Default clocking for all properties
   default clocking axi4_aclk @(posedge ACLK); endclocking

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                          Helper logic                           *
    *            ><><><><><><><><><><><><><><><><><><><><             */

   // Configure unsupported AXI4-Lite signals
   logic  W_unsupported_sig;
   assign W_unsupported_sig = (/* All bursts are defined to be of length 1,
                                * equivalent to a WLAST or RLAST value of 1. */
                               WLAST  == 1'b1 &&
                               /* Optional User-defined signal in the write address channel.
                                * Supported only in AXI4. */
                               WUSER   == {cfg.WUSER_WIDTH{1'b0}});

   /* There is one write strobe for each eight bits of the write data
    * bus, therefore WSTRB[n] corresponds to WDATA[(8n)+7: (8n)].
    * (Section A3.4.3 Data read and write structure, pA3-52). */
   logic [cfg.DATA_WIDTH-1:0] mask_wdata;
   logic full_wstrb;
   logic masked_wstrb;
   for (genvar n = 0; n < STRB_WIDTH; n++) begin: mask_valid_byte_lanes
      assign mask_wdata[(8*n)+7:(8*n)] = {8{WSTRB[n]}};
   end
   always_comb begin
      full_wstrb = (WSTRB=={STRB_WIDTH{1'b1}});
      masked_wstrb = (WSTRB!={STRB_WIDTH{1'b1}});
   end

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *            Section B1.1: Definition of AXI4-Lite                *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.PROTOCOL_TYPE == AXI4LITE) begin: axi4lite_defs
	 // Configure the AXI4-Lite checker unsupported signals.
         cp_W_unsupported_axi4l: assume property(disable iff (!ARESETn) axi4_lite_unsupported_sig(W_unsupported_sig))
           else $error("Violation: For W in AXI4-Lite, only signals described in B1.1 are",
                       "required or supported (B1.1 Definition of AXI4-Lite, pB1-126).");
         if(cfg.CHECK_PARAMETERS == 1) begin: check_dataw
            ap_W_AXI4LITE_DATAWIDTH: assert property(axi4l_databus_width(cfg.DATA_WIDTH))
              else $error("Violation: AXI4-Lite supports a data bus width of 32-bit or 64-bit",
                          "(B.1 Definition of AXI4-Lite, pB1-126).");
	 end
      end
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                             WDATA                               *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
         ap_W_STABLE_WDATA: assert property(disable iff(!ARESETn) stable_before_handshake(WVALID, WREADY, (WDATA & mask_wdata)))
           else $error("Violation: Once the source has asserted WVALID, data and control information",
		       "from source must remain stable [WDATA] until WREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 if(cfg.ENABLE_XPROP) begin
            ap_W_WDATA_X: assert property(disable iff(!ARESETn) valid_information(WVALID, WDATA))
              else $error("Violation : The source can assert the [W]VALID signal only when it",
                          "drives valid address and control information (A3.2.2 Channel signaling",
                          "requirements pA3-40).");
         end
      end
      else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
         cp_W_STABLE_WDATA: assume property(disable iff(!ARESETn) stable_before_handshake(WVALID, WREADY, (WDATA & mask_wdata)))
           else $error("Violation: Once the source has asserted WVALID, data and control information",
		       "from source must remain stable [WDATA] until WREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 if(cfg.ENABLE_XPROP) begin
            cp_W_WDATA_X: assume property(disable iff(!ARESETn) valid_information(WVALID, WDATA))
              else $error("Violation : The source can assert the [W]VALID signal only when it",
                          "drives valid address and control information (A3.2.2 Channel signaling",
                          "requirements pA3-40).");
         end
      end
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                             WSTRB                               *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	 ap_W_STABLE_WSTRB: assert property(disable iff(!ARESETn) stable_before_handshake(WVALID, WREADY, WSTRB))
           else $error("Violation: Once the source has asserted WVALID, data and control information",
                       "from source must remain stable [WSTRB] until WREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 if(cfg.ENABLE_XPROP) begin
            ap_W_WSTRB_X: assert property(disable iff(!ARESETn) valid_information(WVALID, WSTRB))
              else $error("Violation : The source can assert the [W]VALID signal only when it",
                          "drives valid address and control information (A3.2.2 Channel signaling",
                          "requirements pA3-40).");
	 end
	 if(cfg.OPTIONAL_WSTRB == 1) begin // TODO: Rename the parameter, is not very descriptive
            ap_W_FULL_TRANSACTION_OPTIONAL_WSTRB: assert property(disable iff(!ARESETn) full_data_transaction(WVALID, full_wstrb))
              else $error("Violation: The default value for write strobes is all signals asserted",
                          "if the source is always performing full data width transactions (optional WSTRB)",
                          "(A10.3.4 Write transactions, Table A10-1).");
         end
      end // if (cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR})
      else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
	 cp_W_STABLE_WSTRB: assume property(disable iff(!ARESETn) stable_before_handshake(WVALID, WREADY, WSTRB))
           else $error("Violation: Once the source has asserted WVALID, data and control information",
                       "from source must remain stable [WSTRB] until WREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 if(cfg.ENABLE_XPROP) begin
            cp_W_WSTRB_X: assume property(disable iff(!ARESETn) valid_information(WVALID, WSTRB))
              else $error("Violation : The source can assert the [W]VALID signal only when it",
                          "drives valid address and control information (A3.2.2 Channel signaling",
                          "requirements pA3-40).");
	 end
	 if(cfg.OPTIONAL_WSTRB == 1) begin
            cp_W_FULL_TRANSACTION_OPTIONAL_WSTRB: assume property(disable iff(!ARESETn) full_data_transaction(WVALID, full_wstrb))
              else $error("Violation: The default value for write strobes is all signals asserted",
                          "if the source is always performing full data width transactions (optional WSTRB)",
                          "(A10.3.4 Write transactions, Table A10-1).");
         end
      end
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                             WLAST                               *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
	 if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	    ap_W_STABLE_WLAST: assert property(disable iff(!ARESETn) stable_before_handshake(WVALID, WREADY, WLAST))
              else $error("Violation: Once the source has asserted WVALID, data and control information",
			  "from source must remain stable [WLAST] until WREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
               ap_W_WLAST_X: assert property(disable iff(!ARESETn) valid_information(WVALID, WLAST))
		 else $error("Violation : The source can assert the [W]VALID signal only when it",
                             "drives valid address and control information (A3.2.2 Channel signaling",
                             "requirements pA3-40).");
	    end
	 end
	 else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
	    cp_W_STABLE_WLAST: assume property(disable iff(!ARESETn) stable_before_handshake(WVALID, WREADY, WLAST))
              else $error("Violation: Once the source has asserted WVALID, data and control information",
			  "from source must remain stable [WLAST] until WREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
               cp_W_WLAST_X: assume property(disable iff(!ARESETn) valid_information(WVALID, WLAST))
		 else $error("Violation : The source can assert the [W]VALID signal only when it",
                             "drives valid address and control information (A3.2.2 Channel signaling",
                             "requirements pA3-40).");
	    end
	 end
      end // if (cfg.PROTOCOL_TYPE == AXI4FULL)
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                             WUSER                               *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
	 if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	    ap_W_STABLE_WUSER: assert property(disable iff(!ARESETn) stable_before_handshake(WVALID, WREADY, WUSER))
              else $error("Violation: Once the source has asserted WVALID, data and control information",
			  "from source must remain stable [WUSER] until WREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
               ap_W_WUSER_X: assert property(disable iff(!ARESETn) valid_information(WVALID, WUSER))
		 else $error("Violation : The source can assert the [W]VALID signal only when it",
                             "drives valid address and control information (A3.2.2 Channel signaling",
                             "requirements pA3-40).");
	    end
	 end
	 else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
	    cp_W_STABLE_WUSER: assume property(disable iff(!ARESETn) stable_before_handshake(WVALID, WREADY, WUSER))
              else $error("Violation: Once the source has asserted WVALID, data and control information",
			  "from source must remain stable [WUSER] until WREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
               ap_W_WUSER_X: assume property(disable iff(!ARESETn) valid_information(WVALID, WUSER))
		 else $error("Violation : The source can assert the [W]VALID signal only when it",
                             "drives valid address and control information (A3.2.2 Channel signaling",
                             "requirements pA3-40).");
	    end
	 end
      end // if (cfg.PROTOCOL_TYPE == AXI4FULL)
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                             WVALID                              *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.OPTIONAL_RESET == 1) begin
         if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
            ap_W_EXIT_RESET: assert property(exit_from_reset(ARESETn, WVALID))
              else $error("Violation: WVALID must be low for the first clock edge",
                          "after ARESETn goes high (A3.2.1 Reset, pA3-38, Figure A3-1).");
         end
         else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
            cp_W_EXIT_RESET: assume property(exit_from_reset(ARESETn, WVALID))
              else $error("Violation: WVALID must be low for the first clock edge",
                          "after ARESETn goes high (A3.2.1 Reset, pA3-38, Figure A3-1).");
         end
      end
      if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	 ap_W_AWVALID_until_AWREADY: assert property(disable iff(!ARESETn) valid_before_handshake(WVALID, WREADY))
           else $error("Violation: Once WVALID is asserted it must remain asserted until the handshake",
                       "occurs (A3.2.1 Handshake process, pA3-39).");
	 if(cfg.ENABLE_XPROP) begin
            ap_W_WVALID_X: assert property(disable iff(!ARESETn) valid_information(ARESETn, WVALID))
	      else $error("Violation : The source can assert the [W]VALID signal only when it",
                          "drives valid address and control information (A3.2.2 Channel signaling",
                          "requirements pA3-40).");
	 end
      end
      else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
	 cp_W_AWVALID_until_AWREADY: assume property(disable iff(!ARESETn) valid_before_handshake(WVALID, WREADY))
           else $error("Violation: Once WVALID is asserted it must remain asserted until the handshake",
                       "occurs (A3.2.1 Handshake process, pA3-39).");
	 if(cfg.ENABLE_XPROP) begin
            cp_W_WVALID_X: assume property(disable iff(!ARESETn) valid_information(ARESETn, WVALID))
	      else $error("Violation : The source can assert the [W]VALID signal only when it",
                          "drives valid address and control information (A3.2.2 Channel signaling",
                          "requirements pA3-40).");
	 end
      end
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                              WREADY                             *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
         if(cfg.ENABLE_XPROP) begin
            ap_W_WREADY_X: assert property(disable iff(!ARESETn) valid_information(ARESETn, WREADY))
              else $error("Violation : The source can assert the [W]VALID signal only when it",
                          "drives valid address and control information (A3.2.2 Channel signaling",
                          "requirements pA3-40).");
         end
      end
      else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
         if(cfg.ENABLE_XPROP) begin
            cp_W_WREADY_X: assume property(disable iff(!ARESETn) valid_information(ARESETn, WREADY))
              else $error("Violation : The source can assert the [W]VALID signal only when it",
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
            ap_W_READY_MAXWAIT: assert property(disable iff(!ARESETn) handshake_max_wait(WVALID, WREADY, cfg.MAXWAIT))
              else $error("Violation: WREADY should be asserted within MAXWAIT cycles of WVALID being asserted (AMBA Recommended).");
         end
         else if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, CONSTRAINT}) begin
            cp_W_READY_MAXWAIT: assume property(disable iff(!ARESETn) handshake_max_wait(WVALID, WREADY, cfg.MAXWAIT))
              else $error("Violation: WREADY should be asserted within MAXWAIT cycles of WVALID being asserted (AMBA Recommended).");
         end
      end
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *              Covers To Maximise Debug Information               *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   // Witnessing scenarios stated in the AMBA AXI4 spec
   generate
      if(cfg.ENABLE_COVER == 1) begin: witness
	 wp_WVALID_before_WREADY: cover property(disable iff(!ARESETn) valid_before_ready(WVALID, WREADY))
           $info("Witnessed: Handshake process pA3-39, Figure A3-2 VALID before READY handshake capability.");
         wp_WREADY_before_WVALID: cover property(disable iff(!ARESETn) ready_before_valid(WVALID, WREADY))
           $info("Witnessed: Handshake process pA3-39, Figure A3-3 READY before VALID handshake capability.");
         wp_WVALID_with_WREADY: cover property(disable iff(!ARESETn) valid_with_ready(WVALID, WREADY))
           $info("Witnessed: Handshake process pA3-39, Figure A3-4 VALID with READY handshake capability.");
	 wp_WVALID_WVALID_LAST_BURST: cover property(disable iff(!ARESETn) (WVALID && WREADY && WLAST))
	   $info("Witnessed: The source asserted WLAST indicating it is driving the final write transfer in the burst.");
	 if(cfg.VERIFY_AGENT_TYPE != DESTINATION) begin
	    // Unmasked transaction
            wp_WSTRB_UNMASKED: cover property(disable iff(!ARESETn) (WVALID && WREADY && (full_wstrb)))
              $info("Witnessed: Transaction with all data valid (all WSTRB bits asserted).");
	    if(cfg.FULL_WR_STRB == 0) begin
	       wp_WSTRB_MASKED: cover property(disable iff(!ARESETn) (WVALID && WREADY && (masked_wstrb)))
		 $info("Witnessed: Transaction with all data valid (all WSTRB bits asserted).");
	    end
	 end
      end // block: witness
   endgenerate
endmodule // amba_axi4_write_data_channel
`default_nettype wire

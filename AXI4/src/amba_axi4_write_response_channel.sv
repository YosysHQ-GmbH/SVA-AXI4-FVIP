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
module amba_axi4_write_response_channel
  import amba_axi4_protocol_checker_pkg::*;
   #(parameter axi4_checker_params_t cfg =
     '{ID_WIDTH:          4,
       BUSER_WIDTH:       32,
       VERIFY_AGENT_TYPE: SOURCE,
       PROTOCOL_TYPE:     AXI4LITE,
       ENABLE_COVER:      1,
       ENABLE_XPROP:      1,
       ARM_RECOMMENDED:   1,
       MAXWAIT:           16,
       OPTIONAL_RESET:    1,
       EXCLUSIVE_ACCESS:  0,
       default:           0})
   (input wire                       ACLK,
    input wire 			     ARESETn,
    input wire [cfg.ID_WIDTH-1:0]    BID,
    input wire [1:0] 		     BRESP,
    input wire [cfg.BUSER_WIDTH-1:0] BUSER,
    input wire 			     BVALID,
    input wire 			     BREADY);

   // Import the properties in this scope
   import amba_axi4_definition_of_axi4_lite::*;
   import amba_axi4_single_interface_requirements::*;

   // Default clocking for all properties
   default clocking axi4_aclk @(posedge ACLK); endclocking

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                          Helper logic                           *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   logic  B_unsupported_sig;
   assign B_unsupported_sig = (/* Optional User-defined signal in the write address channel.
                                * Supported only in AXI4. */
                               BUSER   == {cfg.BUSER_WIDTH{1'b0}} &&
                               /* AXI4-Lite does not support AXI IDs. This means
                                * all transactions must be in order, and all
                                * accesses use a single fixed ID value. */
                               BID     == {cfg.ID_WIDTH{1'b0}});

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *            Section B1.1: Definition of AXI4-Lite                *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.PROTOCOL_TYPE == AXI4LITE) begin: axi4lite_defs
         // Configure the AXI4-Lite checker unsupported signals.
         cp_B_unsupported_axi4l: assume property(disable iff(!ARESETn) axi4_lite_unsupported_sig(B_unsupported_sig))
           else $error("Violation: For B in AXI4-Lite, only signals described in B1.1 are",
                       "required or supported (B1.1 Definition of AXI4-Lite, pB1-126).");
      end
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                              BID                                *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.PROTOCOL_TYPE == AXI4FULL) begin
         if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, MONITOR}) begin
            ap_B_STABLE_BID: assert property(disable iff(!ARESETn) stable_before_handshake(BVALID, BREADY, BID))
              else $error("Violation: Once the master has asserted BVALID, data and control information",
                          "from master must remain stable [BID] until BREADY is asserted",
                          "(A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
	       ap_B_BID_X: assert property(disable iff(!ARESETn) valid_information(BVALID, BID))
		 else $error("Violation : The source can assert the [B]VALID signal only when it",
			     "drives valid address and control information (A3.2.2 Channel signaling",
			     "requirements pA3-40).");
	    end
         end
         else if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, CONSTRAINT}) begin
            cp_B_STABLE_BID: assume property(disable iff(!ARESETn) stable_before_handshake(BVALID, BREADY, BID))
              else $error("Violation: Once the master has asserted BVALID, data and control information",
                          "from master must remain stable [BID] until BREADY is asserted",
                          "(A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	    if(cfg.ENABLE_XPROP) begin
	       cp_B_BID_X: assume property(disable iff(!ARESETn) valid_information(BVALID, BID))
		 else $error("Violation : The source can assert the [B]VALID signal only when it",
			     "drives valid address and control information (A3.2.2 Channel signaling",
			     "requirements pA3-40).");
	    end
         end
      end // if (cfg.PROTOCOL_TYPE == AXI4FULL)
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                             BRESP                               *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, MONITOR}) begin
         ap_B_STABLE_BRESP: assert property(disable iff(!ARESETn) stable_before_handshake(BVALID, BREADY, BRESP))
           else $error("Violation: Once the master has asserted BVALID, data and control information",
                       "from master must remain stable [BRESP] until BREADY is asserted",
                       "(A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 if(cfg.ENABLE_XPROP) begin
	    cp_B_BRESP_X: assert property(disable iff(!ARESETn) valid_information(BVALID, BRESP))
	      else $error("Violation : The source can assert the [B]VALID signal only when it",
			  "drives valid address and control information (A3.2.2 Channel signaling",
			  "requirements pA3-40).");
	 end
      end
      else if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, CONSTRAINT}) begin
         cp_B_STABLE_BRESP: assume property(disable iff(!ARESETn) stable_before_handshake(BVALID, BREADY, BRESP))
           else $error("Violation: Once the master has asserted BVALID, data and control information",
                       "from master must remain stable [BRESP] until BREADY is asserted",
                       "(A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 if(cfg.ENABLE_XPROP) begin
	    cp_B_BRESP_X: assume property(disable iff(!ARESETn) valid_information(BVALID, BRESP))
	      else $error("Violation : The source can assert the [B]VALID signal only when it",
			  "drives valid address and control information (A3.2.2 Channel signaling",
			  "requirements pA3-40).");
	 end
      end
      if(cfg.PROTOCOL_TYPE == AXI4LITE || cfg.EXCLUSIVE_ACCESS == 1'b0) begin
	 if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, MONITOR}) begin
	    ap_B_UNSUPPORTED_RESPONSE: assert property(disable iff(!ARESETn) unsupported_transfer_status(BVALID, BRESP, EXOKAY))
              else $error("Violation: The EXOKAY response is not supported on the read data",
                          "and write response channels (B1.1.1 Signal List, pB1-126).");
	 end
	 else if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, CONSTRAINT}) begin
	    cp_B_UNSUPPORTED_RESPONSE: assume property(disable iff(!ARESETn) unsupported_transfer_status(BVALID, BRESP, EXOKAY))
              else $error("Violation: The EXOKAY response is not supported on the read data",
                          "and write response channels (B1.1.1 Signal List, pB1-126).");
	 end
      end
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                             BUSER                               *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, MONITOR}) begin
         ap_B_STABLE_BUSER: assert property(disable iff(!ARESETn) stable_before_handshake(BVALID, BREADY, BUSER))
           else $error("Violation: Once the master has asserted BVALID, data and control information",
                       "from master must remain stable [BUSER] until BREADY is asserted",
                       "(A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 if(cfg.ENABLE_XPROP) begin
	    ap_B_BUSER_X: assert property(disable iff(!ARESETn) valid_information(BVALID, BUSER))
	      else $error("Violation : The source can assert the [B]VALID signal only when it",
			  "drives valid address and control information (A3.2.2 Channel signaling",
			  "requirements pA3-40).");
	 end
      end
      else if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, CONSTRAINT}) begin
         cp_B_STABLE_BUSER: assume property(disable iff(!ARESETn) stable_before_handshake(BVALID, BREADY, BUSER))
           else $error("Violation: Once the master has asserted BVALID, data and control information",
                       "from master must remain stable [BUSER] until BREADY is asserted",
                       "(A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 if(cfg.ENABLE_XPROP) begin
	    cp_B_BUSER_X: assume property(disable iff(!ARESETn) valid_information(BVALID, BUSER))
	      else $error("Violation : The source can assert the [B]VALID signal only when it",
			  "drives valid address and control information (A3.2.2 Channel signaling",
			  "requirements pA3-40).");
	 end
      end
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                             BVALID                              *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.OPTIONAL_RESET == 1) begin
         if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, MONITOR}) begin
            ap_B_EXIT_RESET: assert property(exit_from_reset(ARESETn, BVALID))
              else $error("Violation: BVALID must be low for the first clock edge",
                          "after ARESETn goes high (A3.2.1 Reset, pA3-38, Figure A3-1).");
         end
         else if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, CONSTRAINT}) begin
            cp_B_EXIT_RESET: assume property(exit_from_reset(ARESETn, BVALID))
              else $error("Violation: BVALID must be low for the first clock edge",
                          "after ARESETn goes high (A3.2.1 Reset, pA3-38, Figure A3-1).");
         end
      end
      if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, MONITOR}) begin
	 ap_B_BVALID_until_BREADY: assert property(disable iff(!ARESETn) valid_before_handshake(BVALID, BREADY))
           else $error("Violation: Once BVALID is asserted it must remain asserted until the handshake",
                       "occurs (A3.2.1 Handshake process, pA3-39).");
	 if(cfg.ENABLE_XPROP) begin
	    ap_B_BVALID_X: assert property(disable iff(!ARESETn) valid_information(ARESETn, BVALID))
	      else $error("Violation : The source can assert the [B]VALID signal only when it",
			  "drives valid address and control information (A3.2.2 Channel signaling",
			  "requirements pA3-40).");
	 end
      end
      else if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, CONSTRAINT}) begin
	 cp_B_BVALID_until_BREADY: assume property(disable iff(!ARESETn) valid_before_handshake(BVALID, BREADY))
           else $error("Violation: Once BVALID is asserted it must remain asserted until the handshake",
                       "occurs (A3.2.1 Handshake process, pA3-39).");
	 ap_B_BVALID_X: assume property(disable iff(!ARESETn) valid_information(ARESETn, BVALID))
	   else $error("Violation : The source can assert the [B]VALID signal only when it",
		       "drives valid address and control information (A3.2.2 Channel signaling",
		       "requirements pA3-40).");
      end
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                             BREADY                              *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, MONITOR}) begin
	 if(cfg.ENABLE_XPROP) begin
	    ap_B_BREADY_X: assert property(disable iff(!ARESETn) valid_information(ARESETn, BREADY))
	      else $error("Violation : The source can assert the [B]VALID signal only when it",
			  "drives valid address and control information (A3.2.2 Channel signaling",
			  "requirements pA3-40).");
	 end
      end
      else if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, CONSTRAINT}) begin
	 if(cfg.ENABLE_XPROP) begin
	    ap_B_BREADY_X: assume property(disable iff(!ARESETn) valid_information(BVALID, BREADY))
	      else $error("Violation : The source can assert the [B]VALID signal only when it",
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
         if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
            ap_B_READY_MAXWAIT: assert property(disable iff(!ARESETn) handshake_max_wait(BVALID, BREADY, cfg.MAXWAIT))
              else $error("Violation: BREADY should be asserted within MAXWAIT cycles of BVALID being asserted (AMBA recommended).");
         end
         else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
            cp_B_READY_MAXWAIT: assume property(disable iff(!ARESETn) handshake_max_wait(BVALID, BREADY, cfg.MAXWAIT))
              else $error("Violation: BREADY should be asserted within MAXWAIT cycles of BVALID being asserted (AMBA recommended).");
         end
      end
   endgenerate

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *              Covers To Maximise Debug Information               *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   // Witnessing scenarios stated in the AMBA AXI4 spec
   generate
      if(cfg.ENABLE_COVER == 1) begin: witness
	 wp_BVALID_before_BREADY: cover property(disable iff (!ARESETn) valid_before_ready(BVALID, BREADY))
	   $info("Witnessed: Handshake process pA3-39, Figure A3-2 VALID before READY handshake capability.");
	 wp_BREADY_before_BVALID: cover property(disable iff (!ARESETn) ready_before_valid(BVALID, BREADY))
	   $info("Witnessed: Handshake process pA3-39, Figure A3-3 READY before VALID handshake capability.");
	 wp_BVALID_with_BREADY: cover property(disable iff (!ARESETn) valid_with_ready(BVALID, BREADY))
	   $info("Witnessed: Handshake process pA3-39, Figure A3-4 VALID with READY handshake capability.");
	 if (cfg.PROTOCOL_TYPE != AXI4LITE) begin: exok_resp
	    wp_WRITE_RESP_EXOKAY: cover property(disable iff (!ARESETn) rdwr_response_exokay(BVALID, BREADY, BRESP))
	      $info("Witnessed: EXOKAY, exclusive access success, A3-58 with Table A3-4.");
	 end
	 wp_WRITE_RESP_OKAY: cover property(disable iff (!ARESETn) rdwr_response_okay(BVALID, BREADY, BRESP))
	   $info("Witnessed: OKAY, normal access success, A3-57 with Table A3-4.");
	 wp_WRITE_RESP_SLVERR: cover property(disable iff (!ARESETn) rdwr_response_slverr(BVALID, BREADY, BRESP))
	   $info("Witnessed: SLVERR, slave error, A3-57 with Table A3-4.");
	 wp_WRITE_RESP_DECERR: cover property(disable iff (!ARESETn) rdwr_response_decerr(BVALID, BREADY, BRESP))
	   $info("Witnessed: DECERR, decode error, A3-57 with Table A3-4.");
      end
   endgenerate
endmodule // amba_axi4_write_response_channel
`default_nettype wire

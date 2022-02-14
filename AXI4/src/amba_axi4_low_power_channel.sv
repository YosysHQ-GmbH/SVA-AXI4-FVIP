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
module amba_axi4_low_power_channel
  import amba_axi4_protocol_checker_pkg::*;
   #(parameter axi4_checker_params_t cfg =
     '{VERIFY_AGENT_TYPE: SOURCE,
       PROTOCOL_TYPE:     AXI4LITE,
       ENABLE_COVER:      1,
       OPTIONAL_RESET:    1,
       OPTIONAL_LP:       1,
       default: 0})
   (input wire ACLK,
    input wire ARESETn,
    // Low Power Interface
    input wire CSYSREQ,
    input wire CSYSACK,
    input wire CACTIVE);

   // Import the properties in this scope
   import amba_axi4_low_power_interface::*;
   import amba_axi4_single_interface_requirements::exit_from_reset;

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		               Helper logic                           *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */
   // Configure optional Low-power interface
   bit LP_optional_sig;
   assign LP_optional_sig = (/* From ARM DUI 0534B, optional
			      * low-power signals are tied to 1. */
			     CSYSREQ == 1'b1 &&
			     CSYSACK == 1'b1 &&
			     CACTIVE == 1'b1);

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                  Optional Low Power Interface                   *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.OPTIONAL_LP == 0) begin: optional_lp_iface
         cp_LP_optional_checks: assume property(@(posedge ACLK) disable iff (!ARESETn)
						LP_optional_sig)
           else $error("Info: If cfg.OPTIONAL_LP is disabled, Low Power Interface signals",
                       "will assume a default value of HIGH, as stated in ARM DUI 0534B",
		       "(2.3, p2-4).");
      end
   endgenerate

   generate
      if(cfg.OPTIONAL_LP == 1 && cfg.OPTIONAL_RESET == 1) begin
	 if(cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR}) begin
	    cp_LP_EXIT_RESET_CSYSREQ: assume property(@(posedge ACLK) exit_from_reset(ARESETn, CSYSREQ))
	      else $error("Violation: CSYSREQ must be low for the first clock edge",
			  "after ARESETn goes high (Note: this is an implicit requirement",
			  "from A9.2.2 Power-down or power-up handshake as LP signals are",
			  "governed by the `system clock controller`, so the values after",
			  "reset rule applies here as well).");
	    ap_LP_EXIT_RESET_CSYSACK: assert property(@(posedge ACLK) exit_from_reset(ARESETn, CSYSACK))
	      else $error("Violation: CSYSACK must be low for the first clock edge",
			  "after ARESETn goes high (Note: this is an implicit requirement",
			  "from A9.2.2 Power-down or power-up handshake as LP signals are",
			  "governed by the `system clock controller`, so the values after",
			  "reset rule applies here as well).");
	 end
	 else if(cfg.VERIFY_AGENT_TYPE inside {DESTINATION, CONSTRAINT}) begin
	    ap_LP_EXIT_RESET_CSYSREQ: assert property(@(posedge ACLK) exit_from_reset(ARESETn, CSYSREQ))
	      else $error("Violation: CSYSREQ must be low for the first clock edge",
			  "after ARESETn goes high (Note: this is an implicit requirement",
			  "from A9.2.2 Power-down or power-up handshake as LP signals are",
			  "governed by the `system clock controller`, so the values after",
			  "reset rule applies here as well).");
	    cp_LP_EXIT_RESET_CSYSACK: assume property(@(posedge ACLK) exit_from_reset(ARESETn, CSYSACK))
	      else $error("Violation: CSYSACK must be low for the first clock edge",
			  "after ARESETn goes high (Note: this is an implicit requirement",
			  "from A9.2.2 Power-down or power-up handshake as LP signals are",
			  "governed by the `system clock controller`, so the values after",
			  "reset rule applies here as well).");
	 end // if (cfg.VERIFY_AGENT_TYPE inside {SOURCE, MONITOR})
      end // if (cfg.OPTIONAL_RESET == 1)

      if(cfg.OPTIONAL_LP == 1) begin
	 ap_LP_CSYSREQ_FALL: assert property(disable iff(!ARESETn) csysreq_fall(CSYSREQ, CSYSACK))
	   else $error("Violation: In Figure A9-1, at T1, the system clock controller drives",
		       "CSYSREQ LOW [...]. See that CSYSACK is HIGH when that event occurs",
		       "(A9.2.2 Power-down or power-up handshake, pA9-107, Figure A9-1).");
	 ap_LP_CSYSREQ_RISE: assert property(disable iff(!ARESETn) csysreq_rise(CSYSREQ, CSYSACK))
	   else $error("Violation: In Figure A9-1, at T3, the system clock controller drives",
		       "CSYSREQ HIGH [...]. See that CSYSACK is low when that event occurs",
		       "(A9.2.2 Power-down or power-up handshake, pA9-107, Figure A9-1).");
	 ap_LP_CSYSACK_FALL: assert property(disable iff(!ARESETn) csysack_fall(CSYSACK, CSYSREQ))
	   else $error("Violation: In Figure A9-1, the peripheral acknowledges the request at time T2",
		       "by driving CSYSACK LOW. See that CSYSREQ is low when that event occurs.",
		       "(A9.2.2 Power-down or power-up handshake, pA9-107, Figure A9-1).");
	 ap_LP_CSYSACK_RISE: assert property(disable iff(!ARESETn) csysack_rise(CSYSACK, CSYSREQ))
	   else $error("Violation: In Figure A9-1, at T4, the peripheral drives CSYSACK HIGH",
		       "to acknowledge the exit. See that CSYSREQ is HIGH when that event occurs",
		       "(A9.2.2 Power-down or power-up handshake, pA9-107, Figure A9-1).");
      end // if (cfg.OPTIONAL_LP == 1)
   endgenerate
endmodule // amba_axi4_low_power_channel
`default_nettype wire

# YosysHQ SVA AXI Properties

```
Copyright (C) 2021  Diego H <diego@yosyshq.com>
Copyright (C) 2021  Sandia Corporation

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
```

## AMBA AXI4 Quick Demos

### AMBA AXI4-Stream Examples
* [Example 01: Source to sink (self check)](https://github.com/YosysHQ-GmbH/SVA-AXI4-FVIP/tree/main/AXI4_STREAM/examples/dd01_self_check)
* [Example 02: AXI4-Stream FIFO from Alex Forencich's](https://github.com/YosysHQ-GmbH/SVA-AXI4-FVIP/tree/main/AXI4_STREAM/examples/dd02_axis_fifo)
* [Example 03: AXI4-Stream Mat - mul from rahulsridhar5/PLCgroup10](https://github.com/YosysHQ-GmbH/SVA-AXI4-FVIP/tree/main/AXI4_STREAM/examples/dd03_mat_mul)
* [Example 04: VHDLwhiz FIFO (Mixed VHDL/SystemVerilog](https://github.com/YosysHQ-GmbH/SVA-AXI4-FVIP/tree/main/AXI4_STREAM/examples/dd04_axi_fifo_vhdlwiz)

### AMBA AXI4 Lite Examples
* [Example 01: Spinal HDL Component (lite)](https://github.com/YosysHQ-GmbH/SVA-AXI4-FVIP/tree/main/AXI4/examples/spinal_axi4_lite)
* [Example 02: Synthesis Test (for testing purposes)](https://github.com/YosysHQ-GmbH/SVA-AXI4-FVIP/tree/main/AXI4/examples/synthesis_test/axi4_lite)

#### AMBA AXI4 Full Examples
* [Example 01: AXI Crossbar](https://github.com/YosysHQ-GmbH/SVA-AXI4-FVIP/tree/main/AXI4/examples/axi_crossbar)
* [Example 02: Synthesis Test (for testing purposes)](https://github.com/YosysHQ-GmbH/SVA-AXI4-FVIP/tree/main/AXI4/examples/synthesis_test/axi4_full)

* * *

## Motivation

The goal of this repository is to showcase how to develop Formal Verification IP _(FVIP)_ for communication protocols such as the AMBA AXI standard, and demonstrate the usefulness of such verification IP for both design and verification tasks.

This FVIP follows these pillars:

- Good organisation of the code.
- Debuggability capabilities.
- Documentation and methodologies for quick start.
- Developed using optimised properties for model checking.

The following sections briefly describe these points.

* * *

### Good organisation of the code

This implementation uses the SVA `property` ... `endproperty` constructs to define the rules that are to be proven, and a link to the specification where said behavior is mentioned, as shown in the excerpt below:

* For AXI4-Stream, all properties are defined inside a single FVIP module that can be seen as the main protocol checker:
```verilog
   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *            Section III: Handshake Rules.                        *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   /* ,         ,                                                     * 
    * |\\\\ ////| "Once TVALID is asserted it must remain asserted    * 
    * | \\\V/// |  until the handshake (TVALID) occurs".              * 
    * |  |~~~|  | Ref: 2.2.1. Handshake Protocol, p2-3.               * 
    * |  |===|  |                                                     * 
    * |  |A  |  |                                                     * 
    * |  | X |  |                                                     * 
    *  \ |  I| /                                                      * 
    *   \|===|/                                                       * 
    *    '---'                                                        */
   property tvalid_tready_handshake;
      @(posedge ACLK) disable iff (!ARESETn)
        TVALID && !TREADY |-> ##1 TVALID;
   endproperty // tvalid_tready_handshake
```

* For AXI4-Lite or AXI4-Full, the properties are defined in separate packages, where each package is a section of the **IHI0022E** specification and each of the five channels defined in the  **IHI0022E** spec has its own checker (or module) with properties that only apply to this channel. For more information please see Section 6 Architecture of the Verification Plan User Guide.
```systemverilog
// amba_axi4_transaction_structure.sv: 53
/* ,         ,                                                     *  
 * |\\\\ ////|  "AXI has the following rules governing the use of  *  
 * | \\\V/// |   bursts:                                           *  
 * |  |~~~|  |     * a burst must not cross a 4KB address          *  
 * |  |===|  |       boundary".                                    *  
 * |  |A  |  |   Ref: A3.4.1 Address structure, pA3-46.            *  
 * |  | X |  |                                                     *  
 *  \ |  I| /                                                      *  
 *   \|===|/                                                       *  
 *    '---'                                                        */  
  property burst_cache_line_boundary(valid, burst, cond);  
     (valid && burst == amba_axi4_protocol_checker_pkg::INCR |-> cond);  
  endproperty // burst_cache_line_boundary

----------------------------------------------------------------------
// amba_axi4_write_address_channel.sv: 129
[...]
always_comb begin  
	end_addr = (AWADDR + (AWLEN << AWSIZE));  
    aw_4KB_boundary = AWADDR[cfg.ADDRESS_WIDTH-1:12] 
					== end_addr[cfg.ADDRESS_WIDTH-1:12];  
end
[...]
// amba_axi4_write_address_channel.sv: 946
if(cfg.ADDRESS_WIDTH > 12) begin  
   ap_AW_AWADDR_BOUNDARY_4KB: assert property(disable iff(!ARESETn) 
             burst_cache_line_boundary(AWVALID, AWBURST, aw_4KB_boundary))  
               else $error("Violation: A write burst must not cross a 4KB address", 
                           "boundary (A3.4.1 Address structure, pA3-46).");  
end
```

This increases readability and encapsulates common behaviors easily, so debugging can be less difficult.

* * *

### Debuggability

A message accompanies the assertion in the action block, so when a failure is found by the new VIP, the user can quickly understand the root cause and fix the problem faster.

* For AXI4-Stream, the message leads to the user to the respective section of the specification for further investigation.
```verilog
assert_SRC_TVALID_until_TREADY: assert property (tvalid_tready_handshake)
           else $error ("Protocol Violation: Once TVALID is asserted \ 
                        "it must remain asserted until the handshake",
						"occurs (2.2.1, p2-3).");
```

* For AXI4-Lite/Full, upon failure of a proof where helper logic is involved, the user can bring to the root-cause analysis window, the predicate that is failing, as well as read the message that points to the respective section of the specification for further analysis. In this example, `aw_4KB_boundary` will be HIGH and will only change the state to LOW if its violated, pointing the exact time of the violation, so that the user is not forced to do the calculations manually (as is the case with closed-source AMBA AXI FVIP).
```systemverilog
[...]
// amba_axi4_write_address_channel.sv: 946
if(cfg.ADDRESS_WIDTH > 12) begin  
   ap_AW_AWADDR_BOUNDARY_4KB: assert property(disable iff(!ARESETn) 
             burst_cache_line_boundary(AWVALID, AWBURST, aw_4KB_boundary))  
               else $error("Violation: A write burst must not cross a 4KB address", 
                           "boundary (A3.4.1 Address structure, pA3-46).");  
end
```

* * *

### Documentation

The YosysHQ SVA AXI FVIP also contains an user guide with information about each of the implemented properties, examples, configurations and general methodologies (remember that there is not a single methodology that fits to all the problems). Some of the examples also contains documentation explaining how to use the FVIP for that specific type of models.

See for example, the axi_crossbar example document.

* * *

### Optimised properties for formal verification.
This FVIP contains word-level properties (for SMT solvers) as well as pure Boolean predicates (for SAT solvers). Furthermore, this FVIP is not tied to a specific tool, although the result of some properties requires an SMT solver.

* * *

### Be used as reference for others to see the power of SVA
By correlating the specification with the property block, users can understand why the property was encoded in that way.

Upon failures, the user would be able to quickly understand the issues, since this repository is open source and does not follow the industrial solution where the IP **uses antecedent and consequent of the propositions in an encrypted manner, adding unnecessary complexity to the debug**.


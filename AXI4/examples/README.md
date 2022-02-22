# Examples

## The AMBA validity test
This examples uses the AMBA AXI4 certified set of assertions (for simulation) to perform a Bounded Model Checking (BMC) with the purpose of finding if there is a violation or discrepancy between AMBA assertions and YosysHQ Formal IP. The `Results.xlsx` file shows the result.

### Result expectation
The result of this test is open, that means, each new property added to the YosysHQ Formal IP should pass, and if there is any CEX or discrepancy, the developer should take action.

## The AXI4 crossbar example
This is an AXI4 crossbar found in github. The YosysHQ Formal IP is connected to both crossbar source-destination ports to check for any AXI4 protocol violation. See the `doc` directory to check the results.

### Result expectation
This design is expected to fail and CEX may require some analysis.

## The spinal axi4 lite
A very simple AXI4-lite destination IP written in SpinalHDL. All the files are provided and the RTL is already generated.

### Result expectation
This design is expected to fail and some analysis may be required to confirm CEX.

## The synthesis test
This design creates a tautology as it connects the source with the destination. This test must always pass, and if it fails, either a property verification directive is swapped, or there's some input/parameter forcing vacuity/unreachability.

### Result expectation
This design is expected to always pass.

## The axi4 lite gpio
A "formally verified IP" acting as a destination example.

### Result expectation
Pass (I added an obvious error, but the values after reset and the max delay between handshake are not added by me).

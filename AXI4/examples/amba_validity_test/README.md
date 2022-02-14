# AMBA Validity Test
## Description
This test uses the AMBA certified SVA IP (intended for simulation) as reference to check the validity and satisfiability of the YosysHQ AMBA AXI Formal IP. This test is just a bounded model between formal IP assumptions and formal IP assertions, that uses the AMBA SVA IP as a monitor as well. 
- *Any assertion that pass in the Formal IP but not in the AMBA IP, may probably be a failure*.
- *Any assertion that fails in the AMBA IP, is either a failure or a missing behavior*.

## Notes
The license of the AMBA IP requires any person to accept the terms and conditions to download the source, therefore we provide the wrappers and instantiation files, but the users will need to download the IP by themselves.
**Note:** It is somehow difficult to find the files, here's the [link](https://silver.arm.com/browse/BP063).

## Results
Please see the file `Results.xlsx`.

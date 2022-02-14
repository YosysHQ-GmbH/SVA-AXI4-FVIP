# AXI4 Lite/Full
This section is still in progress.

## Architecture
*Deprecated -> this way of thinking about how to connect the IP is not very natural. Adopting `VERIFY_AGENT_TYPE` parameter to make it easier*.

The AXI4 Lite/Full will be able to be configured as follows:
* **Source**: Assumptions as sink component with assertions for source outputs.
	* Usage: Verify source components.
* **Destination**: Assumptions as source component with assertions for sink outputs.
	* Usage: Verify sink components.

*These are still valid*
* **Constrain**: Assumptions as sink and source components.
	* Usage: 
		* Isolate issues. 
		* Fast verification of external props.
		* RTL-Bringup. 
		* Verify other VIP.
* **Monitor**: Assertions as sink and source components.
	* Usage: 
		* Isolate issues.
		* Verify transactions.
		* End-to-end checks.

---

## Development Plan
The file `AXI4 Lite-No-Extensions Propositions.xlsx` contains the development plan for this VIP.

---

## Templates
There are templates to connect the formal IP under `templates` directory.

---

### Features supported
* Multiple transaction ID.
* In order, out of order transactions.
* Formal optimised assertions.

### Features not supported
* Interleaving.

# Most tools uses a similar command to read verilog
set read_verilog_cmd <command>

# And some standard (2005, 2009 or 2012) can be defined as well
set std_ver <version>

# If there is an special command to read assertions in SVA or PSL define it here
set read_assertions read_sva

# If the tool cannot elaborate assertions and DUT at the same time, set this var to 1
set elab_dut_before_formal_model 1
set elaborate_command <command>
set read_assertions_context_switch_cmd <change context command>

# Read the HDL design unit (DUT)
$read_verilog_cmd $std_ver <dut>.sv

# Read the YosysHQ verification files
$read_verilog_cmd  $std_ver  ../../src/amba_axi4_protocol_checker_pkg.sv
$read_verilog_cmd  $std_ver  ../../src/axi4_spec/amba_axi4_single_interface_requirements.sv
$read_verilog_cmd  $std_ver  ../../src/axi4_spec/amba_axi4_definition_of_axi4_lite.sv
$read_verilog_cmd  $std_ver  ../../src/axi4_spec/amba_axi4_atomic_accesses.sv
$read_verilog_cmd  $std_ver  ../../src/axi4_spec/amba_axi4_transaction_structure.sv
$read_verilog_cmd  $std_ver  ../../src/axi4_spec/amba_axi4_transaction_attributes.sv

$read_verilog_cmd  $std_ver  ./amba_axi4_protocol_checker.sv
$read_verilog_cmd  $std_ver  ../../src/amba_axi4_write_response_channel.sv
$read_verilog_cmd  $std_ver  ../../src/amba_axi4_write_address_channel.sv
$read_verilog_cmd  $std_ver  ../../src/amba_axi4_write_data_channel.sv
$read_verilog_cmd  $std_ver  ../../src/amba_axi4_read_data_channel.sv
$read_verilog_cmd  $std_ver  ../../src/amba_axi4_read_address_channel.sv

# Now the template for binding assertions to the DUT
$read_verilog_cmd $std_ver <template>


if {$elab_dut_before_formal_model == 1} {
    # Elaborate and run
    $elaborate_command -top <top>
    # Change context to elaborate formal model
    $read_assertions_context_switch_cmd
}

#set clock
#set reset
#run checks


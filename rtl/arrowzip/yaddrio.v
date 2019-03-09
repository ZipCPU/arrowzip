////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	yaddrio.v
//
// Project:	ArrowZip, a demonstration of the Arrow MAX1000 FPGA board
//
// Purpose:	Creates a single ended, bi-directional port for both input
//		and output data.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2019, Gisselquist Technology, LLC
//
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of  the GNU General Public License as published
// by the Free Software Foundation, either version 3 of the License, or (at
// your option) any later version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
// for more details.
//
// You should have received a copy of the GNU General Public License along
// with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
// target there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
//
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype none
//
module	yaddrio(i_clk, i_we, i_data, o_data, io_pad);
	input	wire		i_clk;
	output	wire	[1:0]	o_data;
	input	wire	[1:0]	i_data;
	input	wire		i_we;
	inout	wire		io_pad;

	wire	ddr_data_to_obuf, from_pad;
	wire	oe_n;


	(* blackbox *)
	fiftyfivenm_ddio_out #(
		.async_mode("none"),
		.sync_mode("none"),
		.power_up("high"),
		.use_new_clocking_model("true"),
		.bypass_three_quarter_register("true")
	) rawddrio (
		.datainhi(i_data[0]),
		.datainlo(i_data[1]),
		.dataout(ddr_data_to_obuf),
		.clkhi(i_clk),
		.clklo(i_clk),
		.muxsel(i_clk),
		.ena(1'b1),	// Output clock enable
	);

	// No FF, since "USE_ONE_REG_TO_DRIVE_OE is false

	(* blackbox *)
	fiftyfivenm_io_obuf
`ifndef	YOSYS
	#(
		.bus_hold("false"),
		.open_drain_output("false")
	)
`endif
	obuf (
		.i(ddr_data_to_obuf),
		.oe(i_we),
		.o(io_pad)
	);

	(* blackbox *)
	fiftyfivenm_io_ibuf
`ifndef	YOSYS
	#(
		.bus_hold("false")
	)
`endif
	ibuf (
		.i(io_pad),
		.o(from_pad));

`ifdef	YOSYS
	reg	ffp, ffn;

	always @(posedge i_clk)
		ffp <= from_pad;
	always @(negedge i_clk)
		ffn <= from_pad;

	assign	o_data = { ffp, ffn };
`else
	wire	first_ff_out;
	(* blackbox *)
	fiftyfivenm_ff pedge (
		.clk(i_clk),
		.d(from_pad),
		.clrn(1'b1),	// input_aset == aset
		.ena(1'b1),
		.q(first_ff_out)
	);

	(* blackbox *)
	fiftyfivenm_ff nedge (
		.clk(!i_clk),
		.d(first_ff_out),
		.clrn(1'b1),	// input_aset == aset
		.ena(1'b1),	// inclocken_wire = (ENABLE_CLOCK_ENA_PORT)?:1
		.q(o_data[0])
	);

	(* blackbox *)
	fiftyfivenm_ff inff (
		.clk(!i_clk),
		.d(from_pad),
		.clrn(1'b1),
		.ena(1'b1),
		.q(o_data[1])
	);
`endif

// outclock = i_clk
// oe_inclk_wire = i_clk
endmodule

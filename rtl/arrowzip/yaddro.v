////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	yaddro.v
// {{{
// Project:	ArrowZip, a demonstration of the Arrow MAX1000 FPGA board
//
// Purpose:	Create a single ended, single directional output port that
//		will toggle on both halves of the clock
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2019-2021, Gisselquist Technology, LLC
// {{{
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
// }}}
module	yaddro (
		// {{{
		// (i_clk, i_data, o_pad);
		input	wire		i_clk,
		input	wire	[1:0]	i_data,
		inout	wire		o_pad
		// }}}
	);

	wire	ddr_data_to_obuf;

	(* blackbox *)
	fiftyfivenm_ddio_out #(
		// {{{
		.async_mode("none"),
		.sync_mode("none"),
		.power_up("high"),
		.use_new_clocking_model("true"),
		.bypass_three_quarter_register("true")
		// }}}
	) rawddr (
		// {{{
		.datainhi(i_data[0]),
		.datainlo(i_data[1]),
		.dataout(ddr_data_to_obuf),
		.clkhi(i_clk),
		.clklo(i_clk),
		.muxsel(i_clk),
		.ena(1'b1),	// Output clock enable
		// }}}
	);

	(* blackbox *)
	fiftyfivenm_io_obuf #(
		// {{{
		.bus_hold("false"),
		.open_drain_output("false")
		// }}}
	) obuf (
		// {{{
		.i(ddr_data_to_obuf),
		.oe(1'b1),
		.o(o_pad),
		.obar()
		// }}}
	);

endmodule

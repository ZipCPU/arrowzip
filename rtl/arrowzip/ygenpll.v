////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	ygenpll.v
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
module	ygenpll(i_clk, o_ck0, o_ck1);
	input	wire		i_clk;
	output	wire		o_ck0;
	output	wire		o_ck1;

	wire	[4:0]	pll_outputs;
	wire		feedback;

	(* blackbox *)
	fiftyfivenm_pll #(
		.bandwidth_type("auto"),
		//
		.clk0_divide_by(3),
		.clk0_duty_cycle(50),
		.clk0_multiply_by(20),
		.clk0_phase_shift("0"),
		//
		.clk1_divide_by(3),
		.clk1_duty_cycle(50),
		.clk1_multiply_by(20),
		.clk1_phase_shift("9375"),
		//
		.compensate_clock("clk0"),
		.inclk0_input_frequency("83333"),
		.operation_mode("normal"),
		.pll_type("auto"),
		.lpm_type("fiftyfivenm_pll")
	) basicpll (
		.clk(pll_outputs),
		.fbin(feedback),
		.fbout(feedback),
		.inclk(i_clk),
		.areset(1'b0),
		.clkswitch(1'b0),
		.configupdate(1'b0),
		.pfdena(1'b1),
		.phasecounterselect(3'b0),
		.phasestep(1'b0),
		.phaseupdown(1'b0),
		.scanclk(1'b0),
		.scanclkena(1'b1),
		.scandata(1'b0));

	assign	o_ck0 = pll_outputs[0];
	assign	o_ck1 = pll_outputs[1];
endmodule

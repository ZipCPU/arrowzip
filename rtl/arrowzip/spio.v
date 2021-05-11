////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	spio.v
// {{{
// Project:	ArrowZip, a demonstration of the Arrow MAX1000 FPGA board
//
// Purpose:	
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2017-2021, Gisselquist Technology, LLC
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
// }}}
`ifdef	VERILATOR
`default_nettype none
`endif
//
module	spio(i_clk, i_wb_cyc, i_wb_stb, i_wb_we, i_wb_data, i_wb_sel,
		o_wb_ack, o_wb_stall, o_wb_data,
		i_btn, o_led, o_int);
	parameter	NLEDS=8, NBTN=2;
	input	wire			i_clk;
	input	wire			i_wb_cyc, i_wb_stb, i_wb_we;
	input	wire	[31:0]		i_wb_data;
	input	wire	[3:0]		i_wb_sel;
	output	reg			o_wb_ack;
	output	wire			o_wb_stall;
	output	wire	[31:0]		o_wb_data;
	input	wire	[(NBTN-1):0]	i_btn;
	output	reg	[(NLEDS-1):0]	o_led;
	output	reg			o_int;

	reg		led_demo;
	reg	[(8-1):0]	r_led;
	initial	r_led = 0;
	initial	led_demo = 1'b1;
	always @(posedge i_clk)
	begin
		if ((i_wb_stb)&&(i_wb_we)&&(i_wb_sel[0]))
		begin
			if (!i_wb_sel[1])
				r_led[NLEDS-1:0] <= i_wb_data[(NLEDS-1):0];
			else
				r_led[NLEDS-1:0] <= (r_led[NLEDS-1:0]&(~i_wb_data[(8+NLEDS-1):8]))
					|(i_wb_data[(NLEDS-1):0]&i_wb_data[(8+NLEDS-1):8]);
		end
	end

	wire	[(8-1):0]	o_btn;
	generate if (NBTN > 0)
		debouncer #(NBTN) thedebouncer(i_clk,
			i_btn, o_btn[(NBTN-1):0]);
	endgenerate

	generate if (NBTN < 8)
		assign	o_btn[7:NBTN] = 0;
	endgenerate

	wire	[(8-1):0]	w_sw;
	assign	w_sw = 0;

	always @(posedge i_clk)
		if ((i_wb_stb)&&(i_wb_we)&&(i_wb_sel[3]))
			led_demo <= i_wb_data[24];

	assign	o_wb_data = { 7'h0, led_demo, w_sw, o_btn, r_led };

	reg	[(NBTN-1):0]	last_btn;
	always @(posedge i_clk)
		last_btn <= o_btn[(NBTN-1):0];
	always @(posedge i_clk)
		o_int <= (|((o_btn[(NBTN-1):0])&(~last_btn)));

	wire	[(NLEDS-1):0]	bounced;
	ledbouncer	#(NLEDS, 25)
		knightrider(i_clk, bounced);

	always @(posedge i_clk)
	if (led_demo)
		o_led <= bounced;
	else
		o_led <= r_led[NLEDS-1:0];

	assign	o_wb_stall = 1'b0;
	always @(posedge i_clk)
		o_wb_ack <= (i_wb_stb);

	// Make Verilator happy
	// verilator lint_on  UNUSED
	wire	[33:0]	unused;
	assign	unused = { i_wb_cyc, i_wb_data, i_wb_sel[2] };
	// verilator lint_off UNUSED
endmodule

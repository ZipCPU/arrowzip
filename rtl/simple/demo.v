////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	demo.v
// {{{
// Project:	ArrowZip, a demonstration of the Arrow MAX1000 FPGA board
//
// Purpose:	This is the top level design entity for the simple ArrowZip
//		demo.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2018-2021, Gisselquist Technology, LLC
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
// }}}
// License:	GPL, v3, as defined and found on www.gnu.org,
// {{{
//		http://www.gnu.org/licenses/gpl.html
//
////////////////////////////////////////////////////////////////////////////////
//
`default_nettype	none
// }}}
module	demo(i_clk, o_led, o_uart_tx, o_uart_tx_b);
	input	wire		i_clk;
	output	wire	[7:0]	o_led;
	output	wire		o_uart_tx;	// PIO_02	N2
	output	wire		o_uart_tx_b;	// PIO_06	L3


	wire	s_clk, locked;
	ippll genclk(i_clk, s_clk, locked);

	helloworld #(.INITIAL_UART_SETUP(31'd0868)) // 19.2 kB
		sayhello(s_clk, o_uart_tx);

	assign	o_uart_tx_b = o_uart_tx;

	wire	[7:0]	w_led;
	ledbouncer knightrider(s_clk, w_led);

	assign o_led = (locked) ? w_led : 8'h00;

endmodule

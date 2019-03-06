////////////////////////////////////////////////////////////////////////////////
//
// Filename:	hbconsole.v
//
// Project:	FPGA library
//
// Purpose:	This is a replacement wrapper to the original hbbus.v debugging
//		bus module.  It is intended to provide all of the functionality
//	of hbbus, while ...
//
//	1. Keeping the debugging bus within the lower 7-bits of the byte
//	2. Muxing a 7-bit (ascii) console also in the lower 7-bits of the byte
//	3. Using the top bit to indicate which channel is being referenced.
//		1'b1 for dbgbus, 1'b0 for the console.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2018, Gisselquist Technology, LLC
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
`default_nettype	none
//
module	hbconsole(i_clk, i_rx_stb, i_rx_byte,
		o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data, o_wb_sel,
		i_wb_ack, i_wb_stall, i_wb_err, i_wb_data,
		i_interrupt,
		o_tx_stb, o_tx_data, i_tx_busy,
		i_console_stb, i_console_data, o_console_busy,
		o_console_stb, o_console_data);
	parameter	LGWATCHDOG=19,
			LGINPUT_FIFO=6,
			LGOUTPUT_FIFO=10;
	input	wire		i_clk;
	input	wire		i_rx_stb;
	input	wire	[7:0]	i_rx_byte;
	output	wire		o_wb_cyc, o_wb_stb, o_wb_we;
	output	wire	[29:0]	o_wb_addr;
	output	wire	[31:0]	o_wb_data;
	output	wire	[3:0]	o_wb_sel;
	input	wire		i_wb_ack, i_wb_stall, i_wb_err;
	input	wire	[31:0]	i_wb_data;
	input	wire		i_interrupt;
	output	wire		o_tx_stb;
	output	wire	[7:0]	o_tx_data;
	input	wire		i_tx_busy;
	//
	input	wire		i_console_stb;
	input	wire	[6:0]	i_console_data;
	output	wire		o_console_busy;
	//
	output	reg		o_console_stb;
	output	reg	[6:0]	o_console_data;
	//


	always @(posedge i_clk)
		o_console_stb <= (i_console_stb)&&(i_rx_byte[7] == 1'b0);
	always @(posedge i_clk)
		o_console_data <= i_rx_byte[6:0];


	wire	w_reset;

	//
	//
	// The incoming stream ...
	//
	//
	// First step, convert the incoming bytes into bits
	wire		dec_stb;
	wire	[4:0]	dec_bits;
	hbdechex dechxi(i_clk,
		i_rx_stb, i_rx_byte,
		dec_stb, w_reset, dec_bits);


	// ... that can then be transformed into bus command words
	wire		iw_stb;
	wire	[33:0]	iw_word;
	hbpack	packxi(i_clk, w_reset,
		dec_stb, dec_bits, iw_stb, iw_word);


	//
	// We'll use these bus command words to drive a wishbone bus
	//
	// verilator lint_off UNUSED
	wire		wb_busy;
	// verilator lint_on UNUSED
	wire		ow_stb;
	wire	[33:0]	ow_word;
	hbexec	wbexec(i_clk, w_reset, iw_stb, iw_word, wb_busy,
			ow_stb, ow_word,
			o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data,
				o_wb_sel, i_wb_ack, i_wb_stall, i_wb_err,
				i_wb_data);

	// We'll then take the responses from the bus, and add an interrupt
	// flag to the output any time things are idle.  This also acts
	// as a one-stage FIFO
	// verilator lint_off UNUSED
	wire		int_busy;
	// verilator lint_on UNUSED
	wire		idl_busy, int_stb;
	wire	[33:0]	int_word;
	hbints	addints(i_clk, w_reset, i_interrupt,
			ow_stb,  ow_word,  int_busy,
			int_stb, int_word, idl_busy);

	// 
	// 
	// 
	wire		hb_busy, idl_stb;
	wire	[33:0]	idl_word;
	hbidle	addidles(i_clk, w_reset,
			int_stb, int_word, idl_busy,
			idl_stb, idl_word, hb_busy);

	// We'll then take that ouput from that stage, and disassemble the
	// response word into smaller (5-bit) sized units ...
	wire		hb_stb, hx_busy;
	wire	[4:0]	hb_bits;
	hbdeword unpackx(i_clk, w_reset,
			idl_stb, idl_word, hb_busy,
			hb_stb, hb_bits, hx_busy);

	wire		hx_stb, nl_busy;
	wire	[6:0]	hx_byte;
	// ... that can then be transmitted back down the channel
	hbgenhex genhex(i_clk, w_reset, hb_stb, hb_bits, hx_busy,
			hx_stb, hx_byte, nl_busy);

	wire		fnl_stb;
	wire	[6:0]	fnl_byte;
	//
	// We'll also add carriage return newline pairs any time the channel
	// goes idle
	hbnewline addnl(i_clk, w_reset, hx_stb, hx_byte, nl_busy,
			fnl_stb, fnl_byte, (i_tx_busy)&&(ps_full));

	reg		ps_full;
	reg	[7:0]	ps_data;
	//
	//
	// Let's now arbitrate between the two outputs
	initial	ps_full = 1'b0;
	always @(posedge i_clk)
		if (!ps_full)
		begin
			if (fnl_stb)
			begin
				ps_full <= 1'b1;
				ps_data <= { 1'b1, fnl_byte[6:0] };
			end else if (i_console_stb)
			begin
				ps_full <= 1'b1;
				ps_data <= { 1'b0, i_console_data[6:0] };
			end
		end else if (!i_tx_busy)
		begin
			ps_full <= fnl_stb;
			ps_data <= { 1'b1, fnl_byte[6:0] };
		end

	assign	o_tx_stb = ps_full;
	assign	o_tx_data = ps_data;
	assign	o_console_busy = (fnl_stb)||(ps_full);

	// Make verilator happy
	// verilator lint_off UNUSED
	// wire	unused;
	// assign	unused = fnl_byte[7];
	// verilator lint_on  UNUSED
endmodule


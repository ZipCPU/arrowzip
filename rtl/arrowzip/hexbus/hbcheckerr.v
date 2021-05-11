////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	hbcheckerr.v
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
module	hbcheckerr(i_clk, i_reset, i_astb, i_aword, i_bbusy, o_err);
	parameter	W = 34;
	input	wire			i_clk, i_reset;
	input	wire			i_astb;
	input	wire	[(W-1):0]	i_aword;
	input	wire			i_bbusy;
	output	reg			o_err;

	reg			last_stb, last_busy;
	reg	[(W-1):0]	last_request;
	initial	last_stb = 1'b0;
	initial	last_busy = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		last_stb  <= 1'b0;
		last_busy <= 1'b0;
	end else begin
		last_stb  <= i_astb;
		last_busy <= i_bbusy;
	end

	always @(posedge i_clk)
		last_request <= i_aword;

	always @(posedge i_clk)
	if (i_reset)
		o_err <= 1'b0;
	else
		o_err <= (last_stb)&&(last_busy)
			&&({ last_stb, last_request } != { i_astb, i_aword});
endmodule

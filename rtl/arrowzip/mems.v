////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rtl/arrowzip/mems.v
//
// Project:	ArrowZip, a demonstration of the Arrow MAX1000 FPGA board
//
// Purpose:	This is the LIS3DH SPI controller.  Please reference the
//		data sheet for the LIS3DH when examining this file.
//
//	The LIS3DH consists of a series of registers that can both be read
//	and written.  This particular controller provides both read and write
//	access to the LIS3DH registers.
//
//	One natural way to have done this would be to stall the WB bus while
//	this controller was being accessed.  This stall would amount to
//	up to 250 clock cycles--unacceptable.  So instead, reads or writes
//	to the device take place via writes to this controller.
//
//	Writes to addresses ...
//	 0- 31	Will read the  8-bit register 0-31
//	32- 63	Will read the 16-bit register, starting at register 0-31
//	64- 95	Will *WRITE* to the  8-bit register 0-31
//	96-127	Will *WRITE* to 16-bit register, starting at 0-31
//
//	Certain registers, however, are *illegal* to write to.  These are the
//	*reserved registers*.  The data sheet warns that attempts to write
//	these registers will damage the device.  Hence, there's a protection
//	circuit to prevent these illegal registers from being written to.
//
//	Reads from this controller will always return the last register read,
//	regardless of the address.
//
//	- If the device is busy, the top bit (o_wb_data[31]) will be set, so
//		you can know to read again later for the right value.
//	- If the the last request was for an 8-bit value, the bottom 8-bits
//		[7:0] will return this result
//	- If the the last request was for an 16-bit value, the bottom 16-bits
//		[15:0] will return this result
//
//		According to the LIS3DH data sheet, 16-bit values will start
//		with the lower [7:0] bits and then return the [15:8] bits.
//		To make certain that these values are coherent, OPT_SWAP_ENDIAN
//		is set by default to swap the two octets before returning the
//		answer.
//
//	Look for examples of how to work with this motion sensor in the
//	sw/board directory.  (None exist there .... yet)
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2017-2019, Gisselquist Technology, LLC
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
module	mems(i_clk, i_reset,
		i_wb_cyc, i_wb_stb, i_wb_we, i_wb_addr, i_wb_data,
			o_wb_ack, o_wb_stall, o_wb_data,
			o_int, o_done,
		o_mems_cs_n, o_mems_sck, o_mems_mosi, i_mems_miso,
		i_mems_int, o_debug);
	parameter	SCKBITS = 4;
	parameter	[(SCKBITS-1):0]	SPI_CLK_DIVIDER = 5;
	parameter	[0:0]	OPT_SWAP_ENDIAN = 1;
`ifdef	FORMAL
	parameter [0:0]	F_OPT_COVER = 0;
`endif
	input	wire		i_clk, i_reset;
	//
	input	wire		i_wb_cyc, i_wb_stb, i_wb_we;
	input	wire	[7:0]	i_wb_addr;
	input	wire	[31:0]	i_wb_data;
	//
	output	reg		o_wb_ack;
	output	wire		o_wb_stall;
	output	wire	[31:0]	o_wb_data;
	//
	output	wire	[1:0]	o_int;
	output	reg		o_done;
	//
	output	reg		o_mems_cs_n, o_mems_sck, o_mems_mosi;
	input	wire		i_mems_miso;
	//
	input	wire	[1:0]	i_mems_int;
	//
	output	wire	[31:0]	o_debug;

	reg		short;
	reg	[23:0]	data_reg;
	reg	[24:0]	busy_reg, done_pipe;

	wire		spi_busy;
	reg	[15:0]	read_data;
	wire		done;
	reg	[15:0]	wb_return;
	//
	reg		reserved_register;
	reg		oe;
	wire		auto_addr_increment;


	//
	// The clock divider
	//
	reg			spi_ztimer, spi_request;
	reg	[(SCKBITS):0]	spi_timer;

	initial	spi_ztimer = 1'b0;
	initial	spi_timer = { SPI_CLK_DIVIDER, 1'b0 };
	always @(posedge i_clk)
	if ((spi_ztimer)&&(spi_request))
		spi_timer <= {1'b0, SPI_CLK_DIVIDER-1'b1 };
	else if ((!o_mems_cs_n)&&(spi_ztimer))
		spi_timer <= {1'b0, SPI_CLK_DIVIDER-1'b1 };
	else if (!spi_ztimer)
		spi_timer <= spi_timer - 1'b1;

	always @(posedge i_clk)
	if ((spi_ztimer)&&(spi_request))
		spi_ztimer <= 1'b0;
	else if ((!o_mems_cs_n)&&(spi_ztimer))
		spi_ztimer <= 1'b0;
	else
		spi_ztimer <= (spi_timer[SCKBITS:1] == 0);

`ifdef	FORMAL
	initial	assert(SPI_CLK_DIVIDER > 1);
	always @(*)
		assert(spi_ztimer == (spi_timer == 0));
	always @(*)
		assert(spi_timer <= { SPI_CLK_DIVIDER, 1'b0 });
	always @(*)
	if (!o_mems_cs_n)
		assert(spi_timer <= { 1'b0, SPI_CLK_DIVIDER });
`endif

	always @(*)
	begin
		reserved_register = 0;
		casez(i_wb_addr[5:0])
		6'b00_00??: reserved_register = 1;
		6'b00_010?: reserved_register = 1;
		6'b00_0110: reserved_register = 1;
		//
		6'b00_1110: reserved_register = 1;
		6'b01_0???: reserved_register = 1;
		6'b01_10??: reserved_register = 1;
		6'b01_110?: reserved_register = 1;
		default: begin end
		endcase

		oe = (i_wb_addr[7] && !reserved_register);
	end

	assign	spi_busy = (!spi_ztimer)||(busy_reg[24]);
	assign	auto_addr_increment = 1'b1;

	initial	short = 1'b0;
	initial	spi_request = 1'b0;
	initial	o_mems_sck  = 1'b1;
	initial	o_mems_cs_n = 1'b1;
	initial	busy_reg    = 0;
	initial	data_reg    = 0;
	initial	done_pipe    = 0;
	always @(posedge i_clk)
	begin
		spi_request   <= (i_wb_stb)&&(i_wb_we)&&(!spi_busy);
		if ((i_wb_stb)&&(i_wb_we)&&(!spi_busy))
		begin
			if (i_wb_addr[6])
			begin
				// 16-bit read/write
				data_reg <= { !oe, auto_addr_increment,
					i_wb_addr[5:0], i_wb_data[15:0] };
				busy_reg <= { 25'h1_ff_ff_ff };
				done_pipe <= { 25'h0_00_00_01 };
				short <= 1'b0;
			end else begin
				data_reg <= { !oe, auto_addr_increment,
					i_wb_addr[5:0], i_wb_data[7:0], 8'hf };
				busy_reg <= { 25'h1_ff_ff_00 };
				done_pipe <= { 25'h0_00_01_00 };
				short <= 1'b1;
			end
			o_mems_cs_n <= 1'b0;
			o_mems_sck  <= 1'b1;
			o_mems_mosi <= !i_wb_we;
		end else if (spi_ztimer && !spi_request)
		begin
			if (o_mems_sck)
			begin
				data_reg  <= { data_reg[ 22:0], 1'b0 };
				busy_reg  <= { busy_reg[ 23:0], 1'b0 };
			end

			if ((o_mems_sck)&&(busy_reg[23]))
			begin
				o_mems_sck <= 1'b0;
				o_mems_mosi <= data_reg[23];
				done_pipe <= { done_pipe[23:0], 1'b0 };
			end else if (o_mems_sck)
			begin
				o_mems_cs_n <= 1'b1;
				done_pipe <= 0;
			end

			if (!o_mems_sck)
				o_mems_sck <= 1'b1;
		end
	end
`ifdef	FORMAL
	always @(*)
		if (!busy_reg[24])
			assert((o_mems_sck)&&(o_mems_cs_n));
`endif

	initial	read_data = 16'h0;
	always @(posedge i_clk)
	if ((spi_ztimer)&&(!o_mems_sck))
		read_data <= { read_data[14:0], i_mems_miso };

	assign	done = (!i_reset)&&(spi_ztimer)&&(o_mems_sck)&&(!o_mems_cs_n)&&(done_pipe[24]);

	initial	o_done = 1'b0;
	always @(posedge i_clk)
		o_done <= done;

	initial	wb_return = 0;
	always @(posedge i_clk)
	if (done)
	begin
		if (short)
			wb_return <= {8'h0, read_data[7:0] };
		else if (OPT_SWAP_ENDIAN)
			wb_return <= { read_data[7:0], read_data[15:8] };
		else
			wb_return <= read_data[15:0];
	end

	//
	// Bus returns
	//
	initial	o_wb_ack = 1'b0;
	always @(posedge i_clk)
		o_wb_ack <= (i_wb_stb)&&(!i_reset);
	assign	o_wb_stall = 1'b0;


	assign	o_wb_data = { (spi_busy), 15'h0, wb_return };

	// A three FF synchronizer
	reg	[5:0]	int_pipe;
	always @(posedge i_clk)
		int_pipe <= { int_pipe[3:0], i_mems_int[1:0] };
	// 01, 23, 45
	assign	o_int = int_pipe[2*2+1:2*2];

	assign	o_debug = { spi_busy, spi_busy,
				spi_ztimer, (i_wb_stb)&&(i_wb_we),
				spi_request,
			i_wb_addr[7:0], wb_return[11:0],
			o_int, o_done,
			o_mems_cs_n, o_mems_sck, o_mems_mosi, i_mems_miso
			};
	// Make verilator happy
	// verilator lint_off UNUSED
	wire	[16:0]	unused;
	assign	unused = { i_wb_cyc, i_wb_data[31:16] };
	// verilator lint_on UNUSED
`ifdef	FORMAL
`ifdef	MEMS
`define	ASSUME	assume
`else
`define	ASSUME	assert
`endif

	wire	[1:0]	f_nreqs, f_nacks, f_outstanding;

	fwb_slave #(.AW(8), .F_MAX_REQUESTS(1), .F_LGDEPTH(2))
		fwb(i_clk, i_reset, i_wb_cyc, i_wb_stb, i_wb_we, i_wb_addr,
			i_wb_data, 4'hf,
			o_wb_ack, o_wb_stall, o_wb_data, 1'b0,
			f_nreqs, f_nacks, f_outstanding);

	reg	f_past_valid;
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;
	always @(*)
		if (!f_past_valid)
			`ASSUME(i_reset);

	initial	assert(o_mems_cs_n);
	initial	assert(o_mems_sck);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(spi_ztimer))&&(!$past(i_reset)))
	begin
		assert(o_mems_cs_n == $past(o_mems_cs_n));
		assert(o_mems_sck  == $past(o_mems_sck));
		assert(o_mems_mosi == $past(o_mems_mosi));
	end

	always @(posedge i_clk)
	if((f_past_valid)&&(!$past(spi_busy))&&($past(!i_wb_stb || !i_wb_we)))
		assert(!spi_busy);

	always @(posedge i_clk)
	if (o_mems_cs_n)
		assert(o_mems_sck);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(o_mems_cs_n))&&(
		($stable(o_mems_sck))||(!$past(o_mems_sck))))
		assume($stable(i_mems_miso));

/*
	always @(posedge i_clk)
		cover((f_past_valid)
			&&($past(i_mems_miso)!=i_mems_miso)
			&&(!$past(o_mems_cs_n))
			&&(!o_mems_cs_n));
*/

	reg	[23:0]	f_output_sreg;
	always @(posedge i_clk)
	if (i_reset)
		f_output_sreg <= 0;
	else if ((f_past_valid)&&($rose(o_mems_sck)))
		f_output_sreg <= { f_output_sreg[22:0], o_mems_mosi };

	//
	// Alternate incoming SPI port check
	//
	reg	[15:0]	f_input_sreg;
	reg	[4:0]	f_sck_count;

	initial	f_sck_count = 0;
	always @(posedge i_clk)
	if (o_mems_cs_n)
		f_sck_count <= 0;
	else if ((f_past_valid)&&(!o_mems_cs_n)&&($rose(o_mems_sck)))
		f_sck_count <= f_sck_count + 1'b1;
	else if (o_mems_cs_n)
		f_sck_count <= 0;

	always @(*)
	if (!o_mems_sck)
	begin
		if (short)
			assert(f_sck_count <= 16);
		else
			assert(f_sck_count <= 24);
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&($rose(o_mems_sck)))
		f_input_sreg <= { f_input_sreg[14:0], i_mems_miso };

	//
	// Induction check
	always @(posedge i_clk)
	if (!o_mems_sck)
	begin
		if (f_sck_count == 1)
			assert(read_data[0] == f_input_sreg[0]);
		if (f_sck_count == 2)
			assert(read_data[1:0] == f_input_sreg[1:0]);
		if (f_sck_count == 3)
			assert(read_data[2:0] == f_input_sreg[2:0]);
		if (f_sck_count == 4)
			assert(read_data[3:0] == f_input_sreg[3:0]);
		if (f_sck_count == 5)
			assert(read_data[4:0] == f_input_sreg[4:0]);
		if (f_sck_count == 6)
			assert(read_data[5:0] == f_input_sreg[5:0]);
		if (f_sck_count == 7)
			assert(read_data[6:0] == f_input_sreg[6:0]);
		if (f_sck_count == 8)
			assert(read_data[7:0] == f_input_sreg[7:0]);
		if (f_sck_count == 9)
			assert(read_data[8:0] == f_input_sreg[8:0]);
		if (f_sck_count == 10)
			assert(read_data[9:0] == f_input_sreg[9:0]);
		if (f_sck_count == 11)
			assert(read_data[10:0] == f_input_sreg[10:0]);
		if (f_sck_count == 12)
			assert(read_data[11:0] == f_input_sreg[11:0]);
		if (f_sck_count == 13)
			assert(read_data[12:0] == f_input_sreg[12:0]);
		if (f_sck_count == 14)
			assert(read_data[13:0] == f_input_sreg[13:0]);
		if (f_sck_count == 15)
			assert(read_data[14:0] == f_input_sreg[14:0]);
		if (f_sck_count >= 16)
			assert(read_data[15:0] == f_input_sreg[15:0]);
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(o_done))
	begin
		if (short)
			assert(o_wb_data[30:0] == { 23'h0, f_input_sreg[7:0] });
		else if (OPT_SWAP_ENDIAN)
			assert(o_wb_data[30:0] == { 15'h0, f_input_sreg[7:0], f_input_sreg[15:8] });
		else
			assert(o_wb_data[30:0] == { 15'h0, f_input_sreg[15:0] });
	end

	genvar	k;
	generate for(k=1; k<25; k=k+1)
	begin : CHECK_BUSY

		always @(*)
		if (!busy_reg[k])
		begin
			assert(busy_reg[k:0] == 0);
			assert(done_pipe[k:0] == 0);
		end else if (!busy_reg[k-1])
			assert((done_pipe[k])||(done_pipe == 0));

		always @(*)
		if (done_pipe[k])
		begin
			assert(busy_reg[(k-1):0] == 0);
			assert(done_pipe[(k-1):0] == 0);
		end

		if (k < 24)
			always @(*)
			if (done_pipe[k])
			begin
				assert(done_pipe[24:(k+1)] == 0);
				assert(&busy_reg[24:k]);
			end
	end endgenerate

	always @(posedge i_clk)
	if ((f_past_valid)&&((!$past(i_wb_stb))||($past(spi_busy))))
		assert(short == $past(short));
/*
	reg	[23:0]	f_next_expected_output;
	always @(posedge i_clk)
	if (i_reset)
		f_next_expected_output <= 0;
	else if ((i_wb_stb)&&(!spi_busy)&&(i_wb_we)&&(i_wb_addr[6]))
		f_next_expected_output <= { !i_wb_addr[7], 1'b1, i_wb_addr[5:0], i_wb_data[15:0] };
	else if ((i_wb_stb)&&(!spi_busy)&&(i_wb_we)&&(!i_wb_addr[6]))
		f_next_expected_output <= { f_output_sreg[7:0], !i_wb_addr[7], 1'b0, i_wb_addr[5:0], i_wb_data[7:0] };

	always @(posedge i_clk)
	if (!spi_busy)
		assert(f_output_sreg == f_next_expected_output);
*/
	always @(posedge i_clk)
		if (!o_mems_cs_n)
			assert(spi_timer < { 1'b1, {(SCKBITS){1'b0}} });

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))
			&&($past(done_pipe)!=0)&&($past(i_wb_cyc)))
		assert( ((o_done)&&(done_pipe == 0))||(done_pipe != 0) );

	always @(posedge i_clk)
	begin
		if (short)
			assert(f_sck_count <= 5'd16);
		else
			assert(f_sck_count <= 5'd24);

		if ((f_past_valid)&&($past(!o_mems_cs_n))&&(o_mems_cs_n))
		begin
			if(short)
				assert(f_sck_count == 5'd16);
			else
				assert(f_sck_count == 5'd24);
		end
	end

	always @(posedge i_clk)
	if (short && !o_mems_sck)
	begin
		casez(f_sck_count)
		5'd00: begin end
		5'd01: assert(done_pipe[10]);
		5'd02: assert(done_pipe[11]);
		5'd03: assert(done_pipe[12]);
		5'd04: assert(done_pipe[13]);
		5'd05: assert(done_pipe[14]);
		5'd06: assert(done_pipe[15]);
		5'd07: assert(done_pipe[16]);
		5'd08: assert(done_pipe[17]);
		5'd09: assert(done_pipe[18]);
		5'd10: assert(done_pipe[19]);
		5'd11: assert(done_pipe[20]);
		5'd12: assert(done_pipe[21]);
		5'd13: assert(done_pipe[22]);
		5'd14: assert(done_pipe[23]);
		5'd15: assert(done_pipe[24]);
		5'd16: assert(done_pipe[24]);
		// default: assert(f_sck_count <= 5'd16);
		endcase
		assert(f_sck_count <= 16);
	end else if (!short && !o_mems_sck)
	begin
		case(f_sck_count)
		5'd00: begin end
		5'd01: assert(done_pipe[ 2]);
		5'd02: assert(done_pipe[ 3]);
		5'd03: assert(done_pipe[ 4]);
		5'd04: assert(done_pipe[ 5]);
		5'd05: assert(done_pipe[ 6]);
		5'd06: assert(done_pipe[ 7]);
		5'd07: assert(done_pipe[ 8]);
		5'd08: assert(done_pipe[ 9]);
		5'd09: assert(done_pipe[10]);
		5'd10: assert(done_pipe[11]);
		5'd11: assert(done_pipe[12]);
		5'd12: assert(done_pipe[13]);
		5'd13: assert(done_pipe[14]);
		5'd14: assert(done_pipe[15]);
		5'd15: assert(done_pipe[16]);
		5'd16: assert(done_pipe[17]);
		5'd17: assert(done_pipe[18]);
		5'd18: assert(done_pipe[19]);
		5'd19: assert(done_pipe[20]);
		5'd20: assert(done_pipe[21]);
		5'd21: assert(done_pipe[22]);
		5'd22: assert(done_pipe[23]);
		5'd23: assert(done_pipe[24]);
		5'd24: assert(done_pipe[24]);
		// default: assert(f_sck_count <= 5'd16);
		endcase

		assert(f_sck_count <= 24);
	end

	always @(posedge i_clk)
	if (done_pipe[0])
		assert(!short);

	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	//
	////////////////////////////////////////////////////////////////////////

	always @(posedge i_clk)
	if (f_past_valid)
		cover($rose(o_done) && short && (o_wb_data[15:0] == 16'h0be));
	always @(posedge i_clk)
		cover($rose(o_done) && !short && (o_wb_data[15:0] == 16'hb015));

	always @(posedge i_clk)
	if (F_OPT_COVER)
	begin
		// While this isn't necessary for the proof, and hence it's
		// only used during cover, the assumptions below greatly
		// simplify the look and feel of the cover trace, making it
		// easier to read and see what's going on
		if (!o_mems_cs_n)
		begin
			assume(o_wb_ack || !i_wb_cyc);
			assume(!i_wb_stb);
			assume(!i_wb_we);
			assume(i_wb_addr == 0);
			assume(i_wb_data == 0);
		end
	end

	reg	f_rcvd_short, f_rcvd_word;
	initial	f_rcvd_short = 0;
	initial	f_rcvd_word = 0;
	always @(posedge i_clk)
	if (o_done && short)
		f_rcvd_short = 1;
	always @(posedge i_clk)
	if (o_done && !short)
		f_rcvd_word = 1;

	always @(posedge i_clk)
		cover(f_past_valid && $past(spi_ztimer) && spi_ztimer
			&&!$past(i_reset));
	always @(posedge i_clk)
		cover(f_rcvd_short && i_wb_stb && i_wb_we && !spi_busy);

	always @(posedge i_clk)
		cover(f_rcvd_word && i_wb_stb && i_wb_we && !spi_busy);

`endif
endmodule

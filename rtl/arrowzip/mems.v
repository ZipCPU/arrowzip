////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rtl/mem.v
//
// Project:	ArrowZip, a demonstration of the Arrow MAX1000 FPGA board
//
// Purpose:	
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
			o_wb_stall, o_wb_ack, o_wb_data,
			o_int, o_done,
		o_mems_cs_n, o_mems_sck, o_mems_mosi, i_mems_miso,
		i_mems_int);
	parameter	SCKBITS = 4;
	parameter	[(SCKBITS-1):0]	SPI_CLK_DIVIDER = 5;
	input	wire		i_clk, i_reset;
	//
	input	wire		i_wb_cyc, i_wb_stb, i_wb_we;
	input	wire	[7:0]	i_wb_addr;
	input	wire	[31:0]	i_wb_data;
	//
	output	wire		o_wb_stall;
	output	reg		o_wb_ack, o_done;
	output	wire	[31:0]	o_wb_data;
	//
	input	wire	[1:0]	i_mems_int;
	output	reg		o_mems_cs_n, o_mems_sck, o_mems_mosi;
	input	wire		i_mems_miso;
	//
	output	wire	[1:0]	o_int;


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

	initial	o_wb_ack = 1'b0;
	always @(posedge i_clk)
		o_wb_ack <= (i_wb_stb)&&(!i_reset);
	assign	o_wb_stall = 1'b0;

`ifdef	FORMAL
	assert	property(SPI_CLK_DIVIDER > 1);
	always @(*)
		assert((spi_ztimer)&&(spi_timer == 0)
			||(!spi_ztimer)&&(spi_timer != 0) );

`endif

	reg		short;
	reg	[23:0]	data_reg;
	reg	[24:0]	busy_reg, done_pipe;

	wire	spi_busy;
	assign	spi_busy = (!spi_ztimer)||(busy_reg[24]);

	initial	short = 1'b0;
	initial	spi_request = 1'b0;
	initial	o_mems_sck  = 1'b1;
	initial	o_mems_cs_n = 1'b1;
	initial	busy_reg    = 0;
	initial	data_reg    = 0;
	initial	done_pipe    = 0;
	always @(posedge i_clk)
	begin
		spi_request   <= (i_wb_stb)&&(!spi_busy);
		if ((i_wb_stb)&&(i_wb_we)&&(!spi_busy))
		begin
			if (i_wb_addr[6])
			begin
				// 16-bit read/write
				data_reg <= { !i_wb_addr[7],1'b1,i_wb_addr[5:0],
					i_wb_data[15:0] };
				busy_reg <= { 25'h1_ff_ff_ff };
				done_pipe <= { 25'h0_00_00_01 };
				short <= 1'b0;
			end else begin
				data_reg <= { !i_wb_addr[7],1'b1,i_wb_addr[5:0],
					i_wb_data[7:0], 8'hf };
				busy_reg <= { 25'h1_ff_ff_00 };
				done_pipe <= { 25'h0_00_01_00 };
				short <= 1'b1;
			end
			o_mems_cs_n <= 1'b0;
			o_mems_sck  <= 1'b1;
			o_mems_mosi <= !i_wb_we;
		end else if ((spi_ztimer)&&(!spi_request))
		begin
			if ((o_mems_sck)&&(busy_reg[23]))
			begin
				o_mems_sck <= 1'b0;
				o_mems_mosi <= data_reg[23];
				data_reg <= { data_reg[22:0], 1'b0 };
				busy_reg <= { busy_reg[23:0], 1'b0 };
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

	reg	[15:0]	read_data;
	initial	read_data = 16'h0;
	always @(posedge i_clk)
		if ((spi_ztimer)&&(!o_mems_sck))
			read_data <= { read_data[14:0], i_mems_miso };

	wire	done;
	assign	done = (!i_reset)&&(spi_ztimer)&&(o_mems_sck)&&(!o_mems_cs_n)&&(done_pipe[24]);

	initial	o_done = 1'b0;
	always @(posedge i_clk)
		o_done <= done;

	reg	[15:0]	wb_return;
	always @(posedge i_clk)
	if (done)
	begin
		if (short)
			wb_return <= {8'h0, read_data[7:0] };
		else
			wb_return <= read_data[15:0];
	end

	assign	o_wb_data = { (spi_busy), 15'h0, wb_return };

	// A three FF synchronizer
	reg	[5:0]	int_pipe;
	always @(posedge i_clk)
		int_pipe <= { int_pipe[3:0], i_mems_int[1:0] };
	// 01, 23, 45
	assign	o_int = int_pipe[2*2+1:2*2];

	// Make verilator happy
	// verilator lint_off UNUSED
	wire	[16:0]	unused;
	assign	unused = { i_wb_cyc, i_wb_data[31:16] };
	// verilator lint_on UNUSED
`ifdef	FORMAL
`ifdef	MEMS
	parameter	F_OPT_CLK2FFLOGIC = 1'b0;

	generate if (F_OPT_CLK2FFLOGIC)
	begin : CLK2FFLOGIC_IF
		reg	f_last_clk;

		initial	f_last_clk = 1'b1;
		always @(posedge i_clk)
			f_last_clk <= !f_last_clk;
		always @(*)
			assume(i_clk == f_last_clk);
	end endgenerate
`define	ASSUME	assume
`else
`define	ASSUME	assert
`endif

	wire	[1:0]	f_nreqs, f_nacks, f_outstanding;

	fwb_slave #(.AW(8), .F_MAX_REQUESTS(1), .F_LGDEPTH(2),
		.F_OPT_CLK2FFLOGIC(F_OPT_CLK2FFLOGIC))
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

	generate if (F_OPT_CLK2FFLOGIC)
	begin : STABILITY
		always @($global_clock)
		if ((f_past_valid)&&(!$rose(i_clk)))
			`ASSUME($stable(i_reset));
		else if ((f_past_valid)&&(!$fell(o_mems_sck)))
			`ASSUME($stable(i_mems_miso));

	end endgenerate

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
	if ((f_past_valid)&&(!$past(o_mems_cs_n))&&(
			($past(o_mems_sck)==o_mems_sck)
			||(!$past(o_mems_sck))))
		assume(i_mems_miso == $past(i_mems_miso));

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
	else if ((f_past_valid)&&(o_mems_sck)&&(!$past(o_mems_sck)))
		f_output_sreg <= { f_output_sreg[22:0], o_mems_mosi };

	reg	[15:0]	f_input_sreg;
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(o_mems_sck))&&(o_mems_sck))
		f_input_sreg <= { f_input_sreg[14:0], i_mems_miso };

	always @(posedge i_clk)
	if ((f_past_valid)&&(o_done))
		begin
			if (short)
				assert(o_wb_data[30:0] == { 23'h0, f_input_sreg[7:0] });
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

	always @(posedge i_clk)
		if (!o_mems_cs_n)
			assert(spi_timer < { 1'b1, {(SCKBITS){1'b0}} });

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))
			&&($past(done_pipe)!=0)&&($past(i_wb_cyc)))
		assert( ((o_done)&&(done_pipe == 0))||(done_pipe != 0) );
	//always @(posedge i_clk)
	//if ((f_past_valid)&&($past(i_reset)))
		//assert(done_pipe == 0);

	reg	[4:0]	f_sck_count;
	initial	f_sck_count = 0;
	always @(posedge i_clk)
	if (o_mems_cs_n)
		f_sck_count <= 0;
	else if ((f_past_valid)&&(!o_mems_cs_n)&&(!$past(o_mems_sck))&&(o_mems_sck))
		f_sck_count <= f_sck_count + 1'b1;

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
		cover(o_done);
`endif
endmodule

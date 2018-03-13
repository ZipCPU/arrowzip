////////////////////////////////////////////////////////////////////////////////
//
// Filename:	dualflexpress.v
//
// Project:	ArrowZip, a demonstration of the Arrow MAX1000 FPGA board
//
// Purpose:	To provide wishbone controlled read access (and read access
//		*only*) to the QSPI flash, using a flash clock of 80MHz, and
//	nothing more.  Indeed, this is designed to be a *very* stripped down
//	version of a flash driver, with the goal of providing 1) very fast
//	access for 2) very low logic count.
//
//	Two modes/states of operation:
//
//	STARTUP
//	 1. Waits for the flash to come on line
//		Start out idle for 300 uS
//	 2. Sends a signal to remove the flash from any QSPI read mode.  In our
//		case, we'll send several clocks of an empty command.  In SPI
//		mode, it'll get ignored.  In QSPI mode, it'll remove us from
//		QSPI mode.
//	 3. Explicitly places and leaves the flash into QSPI mode
//		0xEB 3(0xa0) 0xa0 0xa0 0xa0 4(0x00)
//	 4. All done
//
//	NORMAL-OPS
//	ODATA <- ?, 3xADDR, 0xa0, 0x00, 0x00 | 0x00, 0x00, 0x00, 0x00 ? (22nibs)
//	STALL <- TRUE until closed at the end
//	MODE  <- 2'b10 for 4 clks, then 2'b11
//	CLK   <- 2'b10 before starting, then 2'b01 until the end
//	CSN   <- 0 any time CLK != 2'b11
//
//
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
`define	OPT_FLASH_PIPELINE
module	dualflexpress(i_clk, i_reset,
		i_wb_cyc, i_wb_stb, i_wb_addr,
			o_wb_ack, o_wb_stall, o_wb_data,
		o_dspi_sck, o_dspi_cs_n, o_dspi_mod, o_dspi_dat, i_dspi_dat,
		i_cfg_stb, i_cfg_data, o_cfg_data, o_err);
	parameter [0:0]	OPT_FLASH_PIPELINE = 1'b1;
	parameter [0:0]	F_OPT_CLK2FFLOGIC  = 1'b0;
	localparam	AW=23-2;
	localparam	DW=32;
	input			i_clk, i_reset;
	//
	input			i_wb_cyc, i_wb_stb;
	input		[(AW-1):0] i_wb_addr;
	//
	output	reg		o_wb_ack, o_wb_stall;
	output	reg	[(DW-1):0]	o_wb_data;
	//
	output	wire	[1:0]	o_dspi_sck;
	output	wire		o_dspi_cs_n;
	output	wire	[1:0]	o_dspi_mod;
	output	wire	[1:0]	o_dspi_dat;
	input	wire	[1:0]	i_dspi_dat;
	//
	input	wire		i_cfg_stb;
	input	wire	[8:0]	i_cfg_data;
	output	wire	[9:0]	o_cfg_data;
	output	reg		o_err;

	//
	// User override logic
	//
	wire	cfg_user_request, cfg_user_grant, cfg_user_cs_n, cfg_user_sck,
		cfg_user_miso, cfg_user_mosi;

	//
	//
	// Maintenance / startup portion
	//
	//
	reg		maintenance;
	reg	[14:0]	m_counter;
	reg	[1:0]	m_state;
	reg	[1:0]	m_mod;
	reg		m_cs_n;
	reg	[1:0]	m_clk;
	reg	[31:0]	m_data;
	wire	[1:0]	m_dat;

	initial	maintenance = 1'b1;
	initial	m_counter   = 0;
	initial	m_state     = 2'b00;
	initial	m_cs_n      = 1'b1;
	initial	m_clk       = 2'b11;
	always @(posedge i_clk)
	if ((i_reset)||(cfg_user_grant))
	begin
		maintenance <= 1'b1;
		m_counter   <= 0;
		m_state     <= 2'b00;
		m_cs_n <= 1'b1;
		m_clk  <= 2'b11;
		m_data <= 32'hff_ff_ff_ff;
		m_mod  <= 2'b00; // Normal SPI mode
	end else begin
		if (maintenance)
			m_counter <= m_counter + 1'b1;
		m_mod <= 2'b00; // SPI mode always for maintenance
		case(m_state)
		2'b00: begin
			// Step one: the device may have just been placed into
			// it's power down mode.  Wait for it to fully enter
			// this mode.
			maintenance <= 1'b1;
			if (m_counter[14:0]==15'h7fff) // 24000 is the limit
				m_state <= 2'b01;
			m_cs_n <= 1'b1;
			m_clk  <= 2'b11;
			end
		2'b01: begin
			// Now that the flash has had a chance to start up, feed
			// it with chip selects with no clocks.   This is
			// guaranteed to remove us from any XIP mode we might
			// be in upon startup.  We do this so that we might be
			// placed into a known mode--albeit the wrong one, but
			// a known one.
			maintenance <= 1'b1;
			//
			// 1111 0000 1111 0000 1111 0000 1111 0000
			// 1111 0000 1111 0000 1111 0000 1111 0000
			// 1111 ==> 17 * 4 clocks, or 68 clocks in total
			//
			if (m_counter[14:0] == 15'd138)
				m_state <= 2'b10;
			m_cs_n <= 1'b0;
			m_clk  <= {(2){!m_counter[2]}};
			m_data <= { 32'hbb00_0a00 }; // EB command
			m_data[31:30] <= 2'b11; // just ... not yet
			end
		2'b10: begin
			// Rest, before issuing our initial read command
			maintenance <= 1'b1;
			if (m_counter[14:0] == 15'd138 + 15'd48)
				m_state <= 2'b11;
			m_cs_n <= 1'b1;	// Rest the interface
			m_clk  <= 2'b11;
			m_data <= { 32'hbb_00_0a_00 }; // BB command
			end
		2'b11: begin
			m_cs_n <= 1'b0;
			if (m_counter[14:0] == 15'd138+15'd48+15'd36)
				maintenance <= 1'b0;
			m_clk  <= (m_clk == 2'b11)? 2'b10 : 2'b01;
			if (m_clk == 2'b01) // BB Fast Read Dual I/O Cmd
				m_data <= {m_data[29:0], 2'h0};
			if (m_counter[14:0] >= 15'd138+15'd48+15'd33)
			begin
				m_cs_n <= 1'b1;
				m_clk  <= 2'b11;
			end
			// We depend upon the non-maintenance code to provide
			// our first (bogus) address, mode, dummy cycles, and
			// data bits.
			end
		endcase
	end
	assign	m_dat = { (2){m_data[31]} };

	//
	//
	// Data / access portion
	//
	//
	reg		r_wb_stall;

	reg	[33:0]	data_pipe;
	reg	[1:0]	pre_ack;
	initial	data_pipe = 0;
	always @(posedge i_clk)
	if ((i_wb_stb)&&(!r_wb_stall))
		data_pipe <= { 2'b00, 1'b0, i_wb_addr, 2'b00, 8'ha0 };
	else
		data_pipe <= { data_pipe[31:0], 2'h0 };

	initial	o_err = 1'b0;
	always @(posedge i_clk)
		o_err <= (i_wb_stb)&&(cfg_user_grant);
	assign	o_wb_stall = (r_wb_stall)&&(!o_err);

	always @(posedge i_clk)
	if (cfg_user_grant)
		o_dspi_dat <= { (2){ cfg_user_mosi } };
	else if (maintenance)
		o_dspi_dat <= m_dat;
	else
		o_dspi_dat <= data_pipe[33:32];

	wire	pipe_req;

	generate
	if (OPT_FLASH_PIPELINE)
	begin : OPT_PIPE
		reg	r_pipe_req;
		wire	w_pipe_condition;

		reg	[(AW-1):0]	last_addr;
		always  @(posedge i_clk)
			if ((i_wb_stb)&&(!r_wb_stall))
				last_addr <= i_wb_addr;

		assign	w_pipe_condition =(pre_ack[0])&&(i_wb_stb)&&(r_wb_stall)
				&&(!maintenance)
				&&(!cfg_user_grant)
				&&(!o_dspi_cs_n)
				&&(last_addr + 1'b1 == i_wb_addr);

		initial	r_pipe_req = 1'b0;
		always @(posedge i_clk)
			r_pipe_req <= w_pipe_condition;

		assign	pipe_req = r_pipe_req;
	end else begin
		assign	pipe_req = 1'b0;
	end endgenerate


	initial	pre_ack = 0;
	always @(posedge i_clk)
		if ((i_reset)||(maintenance)||(!i_wb_cyc))
			pre_ack <= 2'b0;
		else if ((i_wb_stb)&&(!r_wb_stall))
			pre_ack <= pre_ack+1'b1;
		else if (o_wb_ack)
			pre_ack <= pre_ack-1'b1;

	reg	[6:0]	clk_ctr;
	initial	clk_ctr = 0;
	always @(posedge i_clk)
	if ((i_reset)||(maintenance))
		clk_ctr <= 0;
	else if ((i_wb_stb)&&(!r_wb_stall))
	begin
		if (!pipe_req)
			clk_ctr <= { 1'b1, 6'd32 };
		else
			clk_ctr <= { 1'b0, 6'd16 };
	end else if (clk_ctr[6])
		clk_ctr[6] <= 1'b0;
	else if (|clk_ctr)
		clk_ctr[5:0] <= clk_ctr[5:0] - 1'b1;

	reg	[15:0]	mod_pipe;
	initial	mod_pipe = 16'hffff;
	always @(posedge i_clk)
	if ((i_reset)||(maintenance))
		mod_pipe <= 16'hffff; // high impedence
	else if(((i_wb_stb)&&(!r_wb_stall)&&(!pipe_req))||(maintenance))
		mod_pipe <= { 16'h0 }; // Always dual, but in/out
	else
		mod_pipe <= { mod_pipe[14:0], 1'b1 }; // Add input at end

	initial	o_dspi_sck = 2'b11;
	always @(posedge i_clk)
	if (i_reset)
		o_dspi_sck <= 2'b11;
	else if (cfg_user_grant)
		o_dspi_sck <= { (2){cfg_user_sck} };
	else if (maintenance)
		o_dspi_sck <= m_clk;
	else if (clk_ctr[6])
		o_dspi_sck <= 2'b10;
	else if (clk_ctr[5:0] != 0)
		o_dspi_sck <= 2'b01;
	else
		o_dspi_sck <= 2'b11;

	initial	o_dspi_cs_n = 1'b1;
	always @(posedge i_clk)
	if (i_reset)
		o_dspi_cs_n <= 1'b1;
	else if (cfg_user_grant)
		o_dspi_cs_n <= cfg_user_cs_n;
	else if (maintenance)
		o_dspi_cs_n <= m_cs_n;
	else
		o_dspi_cs_n <= (clk_ctr == 0);

	initial	o_dspi_mod = 2'b00; // Normal SPI mode
	always @(posedge i_clk)
	if (i_reset)
		o_dspi_mod <=2'b00;
	else if (cfg_user_grant)
		o_dspi_mod <=2'b00;
	else if (maintenance)
		o_dspi_mod <= m_mod;
	else
		o_dspi_mod <= (mod_pipe[15]? 2'b11:2'b10);

	reg	[5:0]	busy_ctr;
	initial	busy_ctr = 6'h0;
	always @(posedge i_clk)
	if (maintenance)
		busy_ctr <= 6'd1;
	else if ((i_wb_stb)&&(!r_wb_stall)&&(!pipe_req))
		busy_ctr <= 6'd34;
	else if ((i_wb_stb)&&(!r_wb_stall))
		busy_ctr <= 6'd17;
	else if (|busy_ctr)
		busy_ctr <= busy_ctr - 1'b1;


	initial	r_wb_stall = 1'b1;
	always @(posedge i_clk)
	if (i_reset)
		r_wb_stall <= 1'b1;
	else if ((maintenance)||(cfg_user_request)||(cfg_user_grant))
		r_wb_stall <= 1'b1;
	else if ((i_wb_stb)&&(pipe_req)&&(busy_ctr == 3))
		r_wb_stall <= 1'b0;
	else
		r_wb_stall <= ((i_wb_stb)&&(!r_wb_stall))
			||(busy_ctr != 0);

	reg	ack_pipe;
	initial	ack_pipe = 1'b0;
	always @(posedge i_clk)
		ack_pipe <= (busy_ctr == 6'd2);

	initial	o_wb_ack = 1'b0;
	always @(posedge i_clk)
		o_wb_ack <= (|pre_ack)&&(ack_pipe)&&(i_wb_cyc)&&(!i_reset);

	always @(posedge i_clk)
		o_wb_data <= { o_wb_data[29:0], i_dspi_dat };

	initial	cfg_user_request = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		cfg_user_request <= 1'b0;
	else if (i_cfg_stb)
		cfg_user_request <= (!i_cfg_data[8])&&(i_cfg_data[3]);

	initial	cfg_user_grant = 1'b0;
	always @(posedge i_clk)
	if ((o_dspi_cs_n)&&(r_wb_stall)&&(busy_ctr <= 1))
		cfg_user_grant <= cfg_user_request;
	else if ((cfg_user_grant)&&(!cfg_user_request))
		cfg_user_grant <= cfg_user_request;


	assign	cfg_user_cs_n = i_cfg_data[3];
	assign	cfg_user_sck  = i_cfg_data[2];
	assign	cfg_user_miso = i_dspi_dat[1];
	assign	cfg_user_mosi = i_cfg_data[0];

	assign	o_cfg_data = { !cfg_user_grant, !cfg_user_request,
			4'h0, cfg_user_cs_n, cfg_user_sck,
			cfg_user_mosi, cfg_user_miso
			};


	// verilator lint_off UNUSED
	wire	[5:0]	unused;
	assign	unused = { i_cfg_data[7:4], i_cfg_data[1], m_data[30] };
	// verilator lint_on  UNUSED






`ifdef	FORMAL
	localparam	F_LGDEPTH=5;
	reg	f_past_valid;
	wire	[(F_LGDEPTH-1):0]	f_nreqs, f_nacks,
					f_outstanding;
	reg	[(AW-1):0]	f_last_pc;
	reg			f_last_pc_valid;
	reg	[(AW-1):0]	f_req_addr;
//
//
// Generic setup
//
//
`ifdef	DUALFLEXPRESS
`define	ASSUME	assume

	generate if (F_OPT_CLK2FFLOGIC)
	begin
		// Assume a clock

		reg	f_last_clk;
		initial	assume(f_last_clk == 1);
		initial	assume(i_clk == 0);
		always @($global_clock)
		begin
			assume(i_clk != f_last_clk);
			f_last_clk <= !f_last_clk;
		end
	end endgenerate

`else
`define	ASSUME	assert
`endif

	// Keep track of a flag telling us whether or not $past()
	// will return valid results
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid = 1'b1;

	assume property(i_reset == !f_past_valid);

	/////////////////////////////////////////////////
	//
	//
	// Assumptions about our inputs
	//
	//
	/////////////////////////////////////////////////

	//
	// Nothing changes, but on the positive edge of a clock
	//
	generate if (F_OPT_CLK2FFLOGIC)
	begin

		always @($global_clock)
		if (!$rose(i_clk))
		begin
			// Control inputs from the CPU
			`ASSUME($stable(i_reset));
			`ASSUME($stable(i_new_pc));
			`ASSUME($stable(i_clear_cache));
			`ASSUME($stable(i_stalled_n));
			`ASSUME($stable(i_pc));
		end
	end endgenerate

	fwb_slave #(.AW(AW), .DW(DW),.F_LGDEPTH(F_LGDEPTH),
			.F_LGDEPTH(F_LGDEPTH),
			.F_MAX_REQUESTS(2),
			.F_MAX_STALL(36),
			.F_MAX_ACK_DELAY(36),
			.F_OPT_RMW_BUS_OPTION(0),
			.F_OPT_CLK2FFLOGIC(F_OPT_CLK2FFLOGIC),
			.F_OPT_DISCONTINUOUS(1))
		f_wbm(i_clk, i_reset,
			i_wb_cyc, i_wb_stb, 1'b0, i_wb_addr, 32'h00, 4'h0,
			o_wb_ack, o_wb_stall, o_wb_data, o_err,
			f_nreqs, f_nacks, f_outstanding);


	always @(posedge i_clk)
		if ((f_past_valid)&&($past(pipe_req))&&($past(o_wb_stall))
				&&($past(i_wb_stb))&&(!$past(o_wb_ack)))
			assert($stable(pipe_req));

	always @(*)
	if (maintenance)
		assume(!i_wb_stb);

	always @(*)
	if (maintenance)
		assert(r_wb_stall);

	/*
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(maintenance)))
		assert(m_counter == $past(m_counter)+1'b1);

	always @(posedge i_clk)
		if ((f_past_valid)&&($past(maintenance)))
			assert(m_counter <= 15'd138+15'd48+15'd10);
		else
			assert(m_counter == 15'd138+15'd48+15'd10);
	*/

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(maintenance))&&(!$past(cfg_user_grant)))
		assert(o_dspi_mod[1]);

	wire	f_wr, f_rd;
	assign	f_rd = ( o_dspi_mod[0]);
	assign	f_wr = (!o_dspi_mod[0]);	// Write to flash

	// FD is the number of clocks in a transaction.  We'll add a little
	// buffer, but that's basically what it is
	localparam	FD = 32;

	wire	[FD-1:0]	f_cs_n, f_dir;
	wire	[2*FD-1:0]	f_sck, f_dat;

	initial	f_cs_n = {(FD){1'b1}};
	initial	f_sck  = {(2*FD){1'b1}};
	initial	f_dat  = {(2*FD){1'b1}};
	initial	f_dir  = {(FD){1'b1}};
	always @(posedge i_clk)
		if ((!f_past_valid)||(i_reset)||(maintenance))
		begin
			f_cs_n <= {(FD){1'b1}};
			f_sck  <= {(2*FD){1'b1}};
			f_dat <= {(2*FD){1'b1}};
			f_dir  <= {(FD){1'b1}};
/*		end else if ((f_past_valid)&&(!$past(o_wb_stall))
			&&(o_dspi_cs_n)&&($past(o_dspi_cs_n))
			&&($past(i_wb_cyc)))
		begin
*/
		end else if ((f_past_valid)&&(i_wb_stb)&&(!o_wb_stall)
				&&(!pipe_req))
		begin
			f_cs_n <= {(FD){1'b1}};
			f_sck  <= {(2*FD){1'b1}};
			f_dat  <= {(2*FD){1'b1}};
			f_dir  <= {(FD){1'b1}};
		end else begin
			f_cs_n <= { f_cs_n[  (FD-2):0], o_dspi_cs_n };
			f_sck  <= { f_sck[ (2*FD-3):0],  o_dspi_sck  };
			f_dat  <= { f_dat[(2*FD-3):0],
					(f_rd) ? i_dspi_dat : o_dspi_dat };
			f_dir  <= { f_dir[   (FD-2):0],  f_wr };
		end

	always @(*)
	if ((!maintenance)&&(!cfg_user_grant)&&(o_dspi_cs_n))
		assert(&o_dspi_sck);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!maintenance)
			&&(!cfg_user_grant)&&($past(o_dspi_cs_n))
			&&(!o_dspi_cs_n))
		assert(o_dspi_sck == 2'b10);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!maintenance)
			&&(!cfg_user_grant)
			&&(!o_dspi_cs_n))
	begin
		if (($past(o_dspi_sck)==2'b01)||($past(o_dspi_sck == 2'b10)))
			assert(!o_dspi_sck[1]);
	end

	integer ik;
	always @(posedge i_clk)
	if ((f_past_valid)&&(!maintenance)
			&&(!cfg_user_grant)
			&&(!o_dspi_cs_n))
	begin
		for(ik=0; ik<FD; ik=ik+1)
		begin
			if (f_cs_n[ik])
				assert(f_sck[(2*ik+1):(2*ik)]==2'b11);
			// if (f_cs_n[ik]) assert(f_dir[ik]);
		end

	
		for(ik=0; ik<FD-1; ik=ik+1)
		begin
			if (f_sck[(2*ik+1):(2*ik)]==2'b10)
				assert(f_sck[(2*ik+3):(2*ik+2)]==2'b11);
			if (f_sck[(2*ik+1):(2*ik)]==2'b01)
				assert(^f_sck[(2*ik+3):(2*ik+2)]);
			if (f_sck[(2*ik+3):(2*ik+2)]==2'b01)
				assert(!f_sck[(2*ik+1)]);
			if ((!f_dir[ik+1])&&(!f_cs_n[ik+1]))
			begin
				assert(!f_dir[ik]);
				assert(&mod_pipe);
			end

			if ((f_cs_n[ik+1])&&(!f_cs_n[ik]))
				assert(f_dir[ik]);
		end

		for(ik=0; ik<16; ik=ik+1)
		begin
			if ((f_cs_n[ik+1])&&(!f_cs_n[ik]))
				assert(&f_dir[ik:0]);
		end
	end

	always @(*)
		assert(busy_ctr <= 6'd34);

	always @(*)
		if (busy_ctr == 6'd34)
			assert(&f_cs_n);

	always @(posedge i_clk)
	if ((!maintenance)&&(!cfg_user_grant))
		if (f_sck[3:2] == 2'b11)
		begin
			assert(f_cs_n[1]);
			assert((f_sck[1:0] == 2'b10)||(f_sck[1:0] == 2'b11));
			assert(f_cs_n[0] == f_sck[0]);
		end else if (f_sck[3:2] == 2'b10)
		begin
			assert(f_cs_n[1:0] == 2'b00);
			assert(f_sck[1:0] == 2'b01);
		end else if (f_cs_n[1:0] == 2'b01)
		begin
			assert(f_sck[3:2] == 2'b01);
			assert(f_sck[1:0] == 2'b11);
		end else
			// Should *NEVER* be here.
			assert(f_sck[3:2] != 2'b00);

	always @(posedge i_clk)
		for(ik=2; ik<32; ik=ik+1)
			if (f_cs_n[ik-1:ik-2]==2'b10)
				assert(f_cs_n[(ik-2):0] == 2'b00);
	always @(*)
		assert(pre_ack < 2'b11);

	always @(*)
	if (pre_ack==0)
		assert(f_outstanding == 0);

	always @(*)
	if (busy_ctr < 2)
		assert(f_outstanding <= 1);

	always @(*)
	if (busy_ctr > 6'h11)
		assert(f_outstanding <= 1);

	always @(*)
	if (pre_ack)
		assert((f_nreqs == 1)||(f_nreqs == 2));

	always @(*)
	if (busy_ctr > 1)
		assert(!cfg_user_grant);

	always @(*)
	if (cfg_user_grant)
	begin
		assert(f_outstanding == 0);
		assert(r_wb_stall);
	end

	always @(*)
	if (i_wb_stb)
		assume(i_wb_cyc);

	reg	f_piped_req, f_second_ack;

	initial	f_piped_req = 1'b0;
	always @(posedge i_clk)
	if ((pipe_req)&&(!o_wb_stall))
		f_piped_req <= 1'b1;

	initial	f_second_ack = 1'b0;
	always @(posedge i_clk)
	if (o_wb_ack)
		f_second_ack <= 1'b1;

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_wb_stb))&&($past(o_wb_stall))
			&&(i_wb_cyc))
	begin
		assume($stable(i_wb_stb));
		assume($stable(i_wb_addr));
	end

	always @(posedge i_clk)
		cover((f_past_valid)&&(o_wb_ack));

	always @(posedge i_clk)
		cover((o_wb_ack)&&(f_second_ack));

	always @(posedge i_clk)
		cover((f_past_valid)&&(o_err));
`endif
endmodule
// Originally:			   (XPRS)
//   Number of wires:                135
//   Number of wire bits:            556
//   Number of public wires:          30
//   Number of public wire bits:     265
//   Number of memories:               0
//   Number of memory bits:            0
//   Number of processes:              0	(R/O)	(FULL)
//   Number of cells:                413	889	1248
//     FDRE                          168	231	 281
//     LUT1                            6	 23	  23
//     LUT2                           61	 83	 203
//     LUT3                           60	 67	 166
//     LUT4                            9	 29	  57
//     LUT5                            6	 50	  95
//     LUT6                           24	215	 256
//     MUXCY                          35	 59	  59
//     MUXF7                           5	 60	  31
//     MUXF8                           2	  5	  10
//     XORCY                          37	 67	  67


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
`define	SPEED_BIT	10
`define	DIR_BIT		9
`define	USER_BIT_n	8
`define	NORMAL_SPI	2'b00
`define	DUAL_WRITE	2'b10
`define	DUAL_READ	2'b11
//
// 290 raw, 372 w/ pipe, 410 cfg, 499 cfg w/pipe
module	dualflexpress(i_clk, i_reset,
		i_wb_cyc, i_wb_stb, i_cfg_stb, i_wb_we, i_wb_addr,
			o_wb_ack, o_wb_stall, o_wb_data,
		o_dspi_sck, o_dspi_cs_n, o_dspi_mod, o_dspi_dat, i_dspi_dat,
		i_cfg_data, o_cfg_data);
	parameter [0:0]	OPT_FLASH_PIPELINE = 1'b1;
	//
	localparam	AW=24-2;
	localparam	DW=32;
	//
	input	wire			i_clk, i_reset;
	//
	input	wire			i_wb_cyc, i_wb_stb, i_cfg_stb, i_wb_we;
	input	wire	[(AW-1):0]	i_wb_addr;
	//
	output	reg			o_wb_ack, o_wb_stall;
	output	reg	[(DW-1):0]	o_wb_data;
	//
	output	reg	[1:0]	o_dspi_sck;
	output	reg		o_dspi_cs_n;
	output	reg	[1:0]	o_dspi_mod;
	output	reg	[1:0]	o_dspi_dat;
	input	wire	[1:0]	i_dspi_dat;
	//
	input	wire	[10:0]	i_cfg_data;
	output	wire	[10:0]	o_cfg_data;

	//
	// User override logic
	//
	reg	cfg_user_mode, cfg_user_speed, cfg_user_dir;
	wire	cfg_write, cfg_hs_write, cfg_ls_write, cfg_hs_read,
		bus_read, pipe_req;
	//
	assign	bus_read  = (i_wb_stb)&&(!o_wb_stall)&&(!i_wb_we)&&(!cfg_user_mode);
	assign	cfg_write = (i_cfg_stb)&&(!o_wb_stall)&&(i_wb_we)
						&&(!i_cfg_data[`USER_BIT_n]);
	assign	cfg_hs_write = (cfg_write)&&(i_cfg_data[`SPEED_BIT])
					&&(i_cfg_data[`DIR_BIT]);
	assign	cfg_hs_read = (cfg_write)&&(i_cfg_data[`SPEED_BIT])
					&&(!i_cfg_data[`DIR_BIT]);
	assign	cfg_ls_write = (cfg_write)&&(!i_cfg_data[`SPEED_BIT]);


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
	if (i_reset)
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
		m_mod <= `NORMAL_SPI; // SPI mode always for maintenance
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
	reg	[31:0]	data_pipe;
	initial	data_pipe = 0;
	always @(posedge i_clk)
	begin
		if (bus_read)
			data_pipe <= { i_wb_addr, 2'b00, 8'ha0 };

		if ((cfg_write)&&(i_cfg_data[`SPEED_BIT]))
			data_pipe[31:24] <= i_cfg_data[7:0];

		if ((cfg_write)&&(!i_cfg_data[`SPEED_BIT]))
		begin
			data_pipe[30] <= i_cfg_data[7];
			data_pipe[28] <= i_cfg_data[6];
			data_pipe[26] <= i_cfg_data[5];
			data_pipe[24] <= i_cfg_data[4];
			data_pipe[22] <= i_cfg_data[3];
			data_pipe[20] <= i_cfg_data[2];
			data_pipe[18] <= i_cfg_data[1];
			data_pipe[16] <= i_cfg_data[0];
		end

		if (o_wb_stall)
			data_pipe <= { data_pipe[29:0], 2'h0 };


		if (maintenance)
			data_pipe[31:30] <= m_dat;
	end

	assign	o_dspi_dat = data_pipe[31:30];

	reg	pre_ack = 1'b0;
	always @(posedge i_clk)
	if ((i_reset)||(!i_wb_cyc))
		pre_ack <= 1'b0;
	else if ((bus_read)||(cfg_write))
		pre_ack <= 1'b1;

	generate
	if (OPT_FLASH_PIPELINE)
	begin : OPT_PIPE
		reg	r_pipe_req;
		wire	w_pipe_condition;

		reg	[(AW-1):0]	next_addr;
		always  @(posedge i_clk)
			if (!o_wb_stall)
				next_addr <= i_wb_addr + 1;

		assign	w_pipe_condition = (i_wb_stb)&&(pre_ack)
				&&(!cfg_user_mode)
				&&(!o_dspi_cs_n)
				&&(next_addr == i_wb_addr);

		initial	r_pipe_req = 1'b0;
		always @(posedge i_clk)
			r_pipe_req <= w_pipe_condition;

		assign	pipe_req = r_pipe_req;
	end else begin
		assign	pipe_req = 1'b0;
	end endgenerate


	reg	[5:0]	clk_ctr;
	initial	clk_ctr = 0;
	always @(posedge i_clk)
	if ((i_reset)||(maintenance))
		clk_ctr <= 0;
	else if ((bus_read)&&(!pipe_req))
		clk_ctr <= 6'd32;
	else if (bus_read)
		clk_ctr <= 6'd16;
	else if (cfg_ls_write)
		clk_ctr <= 6'd8;
	else if (cfg_write)
		clk_ctr <= 6'd4;
	else if (|clk_ctr)
		clk_ctr <= clk_ctr - 1'b1;

	initial	o_dspi_sck = 2'b11;
	always @(posedge i_clk)
	if (i_reset)
		o_dspi_sck <= 2'b11;
	else if (maintenance)
		o_dspi_sck <= m_clk;
	else if ((bus_read)||(cfg_write))
		o_dspi_sck <= 2'b01;
	else if (clk_ctr[5:0] > 6'd1)
		o_dspi_sck <= 2'b01;
	else
		o_dspi_sck <= 2'b11;

	initial	o_dspi_cs_n = 1'b1;
	always @(posedge i_clk)
	if (i_reset)
		o_dspi_cs_n <= 1'b1;
	else if (maintenance)
		o_dspi_cs_n <= m_cs_n;
	else if ((i_cfg_stb)&&(!o_wb_stall)&&(i_wb_we)
			&&(i_cfg_data[`USER_BIT_n]))
		o_dspi_cs_n <= 1'b1;
	else if ((bus_read)||(cfg_user_mode)||(cfg_write))
		o_dspi_cs_n <= 1'b0;
	else
		o_dspi_cs_n <= (clk_ctr == 0);

	// Control the mode of the external pins
	// 	NORMAL_SPI: i_miso is an input,  o_mosi is an output
	// 	DUAL_READ:  i_miso is an input,  o_mosi is an input
	// 	DUAL_WRITE: i_miso is an output, o_mosi is an output
	initial	o_dspi_mod =  `NORMAL_SPI;
	always @(posedge i_clk)
	if (i_reset)
		o_dspi_mod <= `NORMAL_SPI;
	else if (maintenance)
		o_dspi_mod <= m_mod;
	else if ((bus_read)&&(!pipe_req))
		o_dspi_mod <= `DUAL_WRITE;
	else if ((bus_read)||(cfg_hs_read))
		o_dspi_mod <= `DUAL_READ;
	else if (cfg_hs_write)
		o_dspi_mod <= `DUAL_WRITE;
	else if ((cfg_ls_write)||((cfg_user_mode)&&(!cfg_user_speed)))
		o_dspi_mod <= `NORMAL_SPI;
	else if ((clk_ctr <= 6'd17)&&(!cfg_user_mode))
		o_dspi_mod <= `DUAL_READ;

	initial	o_wb_stall = 1'b1;
	always @(posedge i_clk)
	if (i_reset)
		o_wb_stall <= 1'b1;
	else if ((maintenance)||(cfg_write)||(bus_read))
		o_wb_stall <= 1'b1;
	else if ((i_wb_stb)&&(pipe_req)&&(clk_ctr == 6'd2))
		o_wb_stall <= 1'b0;
	else if (clk_ctr > 1)
		o_wb_stall <= 1'b1;
	else if (cfg_user_mode)
		o_wb_stall <= 1'b0;
	else
		o_wb_stall <= (!o_dspi_cs_n);

	reg	ack_pipe;
	initial	ack_pipe = 1'b0;
	always @(posedge i_clk)
		ack_pipe <= (clk_ctr == 6'd2);

	initial	o_wb_ack = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_wb_ack <= 1'b0;
	else if(((i_wb_stb)||(i_cfg_stb))&&(!o_wb_stall)&&(!bus_read)&&(!cfg_write))
		// Writes are not allowed, they immediately ack after doing
		// nothing.   Reads from the configuration register need no
		// other logic they can also be returned immediately
		o_wb_ack <= 1'b1;
	else
		o_wb_ack <= (pre_ack)&&(ack_pipe)&&(i_wb_cyc)&&(!i_reset);

	always @(posedge i_clk)
	if (!o_dspi_sck[1])
	begin
		if (!o_dspi_mod[1])
			o_wb_data <= { o_wb_data[30:0], i_dspi_dat[1] };
		else
			o_wb_data <= { o_wb_data[29:0], i_dspi_dat };
	end

	//
	//
	//  User override access
	//
	//
	initial	cfg_user_mode = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		cfg_user_mode <= 1'b0;
	else if ((i_cfg_stb)&&(!o_wb_stall)&&(i_wb_we))
		cfg_user_mode = !i_cfg_data[`USER_BIT_n];

	always @(posedge i_clk)
	if ((i_cfg_stb)&&(!o_wb_stall))
	begin
		cfg_user_speed <= ( i_cfg_data[`SPEED_BIT]);
		cfg_user_dir   <= ( i_cfg_data[`DIR_BIT]);
	end

	assign	o_cfg_data = { cfg_user_speed, cfg_user_dir,
			cfg_user_mode, o_wb_data[7:0] };

	// verilator lint_off UNUSED
	wire	[5:0]	unused;
	assign	unused = { i_cfg_data[7:4], i_cfg_data[1], m_data[30] };
	// verilator lint_on  UNUSED

`ifdef	FORMAL
	localparam	F_LGDEPTH=2;
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
`else
`define	ASSUME	assert
`endif

	// Keep track of a flag telling us whether or not $past()
	// will return valid results
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid = 1'b1;

	always @(*)
	if (!f_past_valid)
       		assume(i_reset);

	/////////////////////////////////////////////////
	//
	//
	// Assumptions about our inputs
	//
	//
	/////////////////////////////////////////////////

	always @(*)
		assume((!i_wb_stb)||(!i_cfg_stb));

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(i_wb_stb))&&($past(o_wb_stall)))
		assume(i_wb_stb);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(i_cfg_stb))&&($past(o_wb_stall)))
		assume(i_cfg_stb);

	fwb_slave #(.AW(AW), .DW(DW),.F_LGDEPTH(F_LGDEPTH),
			.F_MAX_STALL(36),
			.F_MAX_ACK_DELAY(68),
			.F_OPT_RMW_BUS_OPTION(0),
			.F_OPT_CLK2FFLOGIC(1'b0),
			.F_OPT_DISCONTINUOUS(1))
		f_wbm(i_clk, i_reset,
			i_wb_cyc, (i_wb_stb)||(i_cfg_stb), i_wb_we, i_wb_addr,
				{ 21'h0, i_cfg_data }, 4'hf,
			o_wb_ack, o_wb_stall, o_wb_data, 1'b0,
			f_nreqs, f_nacks, f_outstanding);

	always @(*)
		assert(f_outstanding <= 2);

	always @(posedge i_clk)
		assert((f_outstanding <= 1)||((o_wb_ack)&&(!o_dspi_cs_n)));

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_wb_stb))||($past(o_wb_stall)))
		assert(f_outstanding <= 1);

	always @(*)
	if (maintenance)
		assume((!i_wb_stb)&&(!i_cfg_stb));

	always @(*)
	if (maintenance)
		assert(f_outstanding == 0);

	always @(*)
	if (maintenance)
	begin
		assert(o_wb_stall);
		//
		assert(clk_ctr == 0);
		assert(cfg_user_mode == 1'b0);
	end

	always @(*)
	if (m_state == 2'b01)
		assert(m_counter <= 15'd138);
	always @(posedge i_clk)
	if (m_state == 2'b10)
		assert(m_counter <= 15'd138 + 15'd48);
	always @(*)
	if (m_state != 2'b11)
		assert(maintenance);
	always @(*)
	if (m_state == 2'b11)
		assert(m_counter <= 15'd138+15'd48+15'd37);
	always @(*)
	if ((m_state == 2'b11)&&(m_counter == 15'd138+15'd48+15'd37))
		assert(!maintenance);
	else if (maintenance)
		assert((m_state!= 2'b11)||(m_counter != 15'd138+15'd48+15'd37));

	always @(*)
	if (maintenance)
		assert(clk_ctr == 0);
	always @(*)
	if (maintenance)
		assert(!o_wb_ack);

	always @(posedge i_clk)
	if (o_wb_ack)
		assert(clk_ctr[3:0] == 0);
	always @(posedge i_clk)
	if ((f_outstanding > 0)&&(clk_ctr > 0))
		assert(pre_ack);
	always @(posedge i_clk)
	if ((i_wb_cyc)&&(o_wb_ack))
		assert(f_outstanding >= 1);

	always @(posedge i_clk)
	if ((f_past_valid)&&(clk_ctr == 0)&&(!o_wb_ack)
			&&((!$past(i_wb_stb|i_cfg_stb))||($past(o_wb_stall))))
		assert(f_outstanding == 0);

	always @(*)
	if ((i_wb_cyc)&&(pre_ack)&&(!o_dspi_cs_n))
		assert((f_outstanding >= 1)||(cfg_user_mode));

	always @(*)
	if ((cfg_user_mode)&&(!o_wb_ack)&&(clk_ctr == 0))
		assert(f_outstanding == 0);

	always @(*)
	if (cfg_user_mode)
		assert(f_outstanding <= 1);
	/////////////////
	//
	// Idle channel
	//
	//
	/////////////////
	always @(*)
	if ((o_dspi_cs_n)&&(!maintenance))
	begin
		assert(clk_ctr == 0);
		assert(o_dspi_sck  == 2'b11);
		//assert((o_dspi_mod == `NORMAL_SPI)||(o_dspi_mod == `DUAL_READ));
	end

	always @(*)
		assert(o_dspi_mod != 2'b01);

	/////////////////
	//
	//  Read requests
	//
	/////////////////
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(bus_read)))
	begin
		assert(!o_dspi_cs_n);
		assert(o_dspi_sck == 2'b01);
		assert(o_dspi_dat == $past(i_wb_addr[21:20]));
		//
		if (!$past(o_dspi_cs_n))
		begin
			assert(clk_ctr == 6'd16);
			assert(o_dspi_mod == `DUAL_READ);
		end else begin
			assert(clk_ctr == 6'd32);
			assert(o_dspi_mod == `DUAL_WRITE);
		end
	end

	always @(*)
		assert(clk_ctr <= 6'd32);

	always @(*)
	if (clk_ctr >= 6'd17)
		assert(o_dspi_mod == `DUAL_WRITE);

	always @(posedge i_clk)
	if ((!OPT_FLASH_PIPELINE)&&(clk_ctr != 0))
		assert(o_wb_stall);
	else if ((OPT_FLASH_PIPELINE)&&(clk_ctr != 0)&&(clk_ctr != 1))
		assert(o_wb_stall);

	/////////////////
	//
	//  User mode
	//
	/////////////////
	always @(*)
	if (maintenance)
		assert(!cfg_user_mode);
	always @(*)
	if (cfg_user_mode)
		assert(!o_dspi_cs_n);

	//
	//
	//
	//
	always @(posedge i_clk)
		cover((f_past_valid)&&(o_wb_ack));

	// always @(posedge i_clk) cover((o_wb_ack)&&(f_second_ack));

`ifdef	VERIFIC

	reg	[21:0]	fv_addr;
	always @(posedge i_clk)
	if (bus_read)
		fv_addr <= i_wb_addr;

	reg	[7:0]	fv_data;
	always @(posedge i_clk)
	if (cfg_write)
		fv_data <= i_cfg_data[7:0];

	// Bus write request
	assert property (@(posedge i_clk)
		(!i_reset)&&(i_wb_stb)&&(!o_wb_stall)&&(i_wb_we)
		|=> (o_wb_ack)&&(o_dspi_cs_n==$past(o_dspi_cs_n)));
	assert property (@(posedge i_clk)
		(!i_reset)&&(i_wb_stb)&&(!o_wb_stall)&&(!i_wb_we)&&(cfg_user_mode)
		|=> (o_wb_ack)&&(!o_dspi_cs_n));
	// Bus read request
	assert property (@(posedge i_clk)
		disable iff (i_reset)
		(i_wb_stb)&&(!o_wb_stall)&&(!i_wb_we)&&(!cfg_user_mode)
			&&(o_dspi_cs_n)
		|=> (((o_wb_stall)&&(!o_dspi_cs_n)&&(o_dspi_sck == 2'b01)
				&&(o_dspi_mod == `DUAL_WRITE)&&(!o_wb_ack)
				&&(f_outstanding <= 1))
			throughout
			(o_dspi_dat == fv_addr[21:20])&&(clk_ctr==6'd32)
			##1 (o_dspi_dat == fv_addr[19:18])&&(clk_ctr==6'd31)
			##1 (o_dspi_dat == fv_addr[17:16])&&(clk_ctr==6'd30)
			##1 (o_dspi_dat == fv_addr[15:14])&&(clk_ctr==6'd29)
			##1 (o_dspi_dat == fv_addr[13:12])&&(clk_ctr==6'd28)
			##1 (o_dspi_dat == fv_addr[11:10])&&(clk_ctr==6'd27)
			##1 (o_dspi_dat == fv_addr[ 9: 8])&&(clk_ctr==6'd26)
			##1 (o_dspi_dat == fv_addr[ 7: 6])&&(clk_ctr==6'd25)
			##1 (o_dspi_dat == fv_addr[ 5: 4])&&(clk_ctr==6'd24)
			##1 (o_dspi_dat == fv_addr[ 3: 2])&&(clk_ctr==6'd23)
			##1 (o_dspi_dat == fv_addr[ 1: 0])&&(clk_ctr==6'd22)
			##1 (o_dspi_dat == 2'b00)&&(clk_ctr==6'd21))
		##1 (((o_wb_stall)&&(!o_dspi_cs_n)&&(o_dspi_sck == 2'b01)
				&&(o_dspi_mod == `DUAL_WRITE)&&(!o_wb_ack)
				&&(f_outstanding <= 1))
			throughout
			(o_dspi_dat == 2'b10)
			##1 (o_dspi_dat == 2'b10)
			##1 (o_dspi_dat == 2'b00)
			##1 (o_dspi_dat == 2'b00)&&(clk_ctr == 6'd17))
		##1 ((o_wb_stall)&&(!o_dspi_cs_n)&&(o_dspi_sck == 2'b01)
				&&(o_dspi_mod == `DUAL_READ)&&(!o_wb_ack)
				&&(f_outstanding <= 1)) [*15]
		##1 ((!o_dspi_cs_n)&&(o_dspi_sck == 2'b01)
				&&(o_dspi_mod == `DUAL_READ)&&(clk_ctr==6'd1)
				&&(!o_wb_ack)
				&&((o_wb_stall)||(OPT_FLASH_PIPELINE))
				&&(f_outstanding <= 1))
		##1 ((o_wb_ack)||(!$past(pre_ack))||($past(!i_wb_cyc))));
			


	// Bus pipe-read request
	assert property (@(posedge i_clk)
		disable iff (i_reset)
		(i_wb_stb)&&(!o_wb_stall)&&(!i_wb_we)&&(!cfg_user_mode)
			&&(!o_dspi_cs_n)&&(OPT_FLASH_PIPELINE)
		|=> (((o_wb_stall)&&(!o_dspi_cs_n)&&(o_dspi_sck == 2'b01)
				&&(o_dspi_mod == `DUAL_READ)&&(o_wb_ack))
				&&((f_outstanding == 2)||(!i_wb_cyc))
				&&(clk_ctr == 6'd16)&&(!cfg_user_mode))
		##1 (((o_wb_stall)&&(!o_dspi_cs_n)&&(o_dspi_sck == 2'b01)
				&&(o_dspi_mod == `DUAL_READ)&&(!o_wb_ack))
				&&((f_outstanding== 1)||(!pre_ack)||(!i_wb_cyc))
				&&(clk_ctr > 0)&&(clk_ctr < 6'd16)
			       		&&(!cfg_user_mode)) [*14]
		##1 (((!o_dspi_cs_n)&&(o_dspi_sck == 2'b01)
				&&(o_dspi_mod == `DUAL_READ)&&(!o_wb_ack))
				&&((f_outstanding== 1)||(!pre_ack)||(!i_wb_cyc))
				&&(clk_ctr == 1))
		##1 (o_wb_ack)||(!$past(pre_ack))||($past(!i_wb_cyc)));

	// Config write    request (low speed)
	assert property (@(posedge i_clk)
		disable iff (i_reset)
		(cfg_ls_write)
		|=> (((o_wb_stall)&&(!o_dspi_cs_n)&&(o_dspi_sck ==2'b01)
			&&(o_dspi_mod == `NORMAL_SPI)&&(!o_wb_ack)
			&&(cfg_user_mode)&&(!cfg_user_speed))
			throughout
			((o_dspi_dat[0] == fv_data[7])&&(clk_ctr == 6'd8))
			##1 ((o_dspi_dat[0] == fv_data[6])&&(clk_ctr == 6'd7))
			##1 ((o_dspi_dat[0] == fv_data[5])&&(clk_ctr == 6'd6))
			##1 ((o_dspi_dat[0] == fv_data[4])&&(clk_ctr == 6'd5))
			##1 ((o_dspi_dat[0] == fv_data[3])&&(clk_ctr == 6'd4))
			##1 ((o_dspi_dat[0] == fv_data[2])&&(clk_ctr == 6'd3))
			##1 ((o_dspi_dat[0] == fv_data[1])&&(clk_ctr == 6'd2))
			##1 ((o_dspi_dat[0] == fv_data[0])&&(clk_ctr == 6'd1)))
			##1((o_wb_ack)||(!$past(pre_ack))||($past(!i_wb_cyc))));

	// Config read-HS  request
	assert property (@(posedge i_clk)
		disable iff (i_reset)
		(cfg_hs_read)
		|=> (((o_wb_stall)&&(!o_dspi_cs_n)&&(o_dspi_sck ==2'b01)
			&&(o_dspi_mod == `DUAL_READ)&&(!o_wb_ack)
			&&(cfg_user_mode)&&(cfg_user_speed)&&(!cfg_user_dir))
			throughout
			(clk_ctr == 6'd4) ##1 (clk_ctr== 6'd3)
			##1 (clk_ctr== 6'd2) ##1 (clk_ctr== 6'd1))
			##1((o_wb_ack)||(!$past(pre_ack))
				||($past(!i_wb_cyc))));

	// Config write-HS request
	assert property (@(posedge i_clk)
		disable iff (i_reset)
		(cfg_hs_write)
		|=> (((o_wb_stall)&&(!o_dspi_cs_n)&&(o_dspi_sck ==2'b01)
			&&(o_dspi_mod == `DUAL_WRITE)&&(!o_wb_ack)
			&&(cfg_user_mode)&&(cfg_user_speed)&&(cfg_user_dir))
			throughout
			((o_dspi_dat[1:0] == fv_data[7:6])&&(clk_ctr == 6'd4))
			##1 ((o_dspi_dat[1:0]==fv_data[5:4])&&(clk_ctr== 6'd3))
			##1 ((o_dspi_dat[1:0]==fv_data[3:2])&&(clk_ctr== 6'd2))
			##1 ((o_dspi_dat[1:0]==fv_data[1:0])&&(clk_ctr== 6'd1)))
			##1((o_wb_ack)||(!$past(pre_ack))||($past(!i_wb_cyc))));

	// Config release  request
	assert property (@(posedge i_clk)
		(!i_reset)&&(i_cfg_stb)&&(!o_wb_stall)&&(i_wb_we)&&(i_cfg_data[`USER_BIT_n])
		|=> (o_wb_ack)&&(o_dspi_cs_n)&&(!cfg_user_mode)
			&&(clk_ctr == 0));

	// Config read-bus request
	assert property (@(posedge i_clk)
		(!i_reset)&&(i_cfg_stb)&&(!o_wb_stall)&&(!i_wb_we)
		|=> (o_wb_ack)&&(o_dspi_cs_n==$past(o_dspi_cs_n))
			&&(clk_ctr==0));


	//
	// Constant data testing
	//
	(* anyconst *)	wire	[21:0]	f_const_addr;
	(* anyconst *)	wire	[31:0]	f_const_data;

	assume property (@(posedge i_clk)
		disable iff ((i_reset)||(!i_wb_cyc))
		(i_wb_stb)&&(!o_wb_stall)&&(!i_wb_we)&&(!cfg_user_mode)
			&&(o_dspi_cs_n)&&(i_wb_addr == f_const_addr)
		|=> 1[*16]
			##1 (i_dspi_dat[1:0] == f_const_data[31:30])
			##1 (i_dspi_dat[1:0] == f_const_data[29:28])
			##1 (i_dspi_dat[1:0] == f_const_data[27:26])
			##1 (i_dspi_dat[1:0] == f_const_data[25:24])
			##1 (i_dspi_dat[1:0] == f_const_data[23:22])
			##1 (i_dspi_dat[1:0] == f_const_data[21:20])
			##1 (i_dspi_dat[1:0] == f_const_data[19:18])
			##1 (i_dspi_dat[1:0] == f_const_data[17:16])
			##1 (i_dspi_dat[1:0] == f_const_data[15:14])
			##1 (i_dspi_dat[1:0] == f_const_data[13:12])
			##1 (i_dspi_dat[1:0] == f_const_data[11:10])
			##1 (i_dspi_dat[1:0] == f_const_data[ 9: 8])
			##1 (i_dspi_dat[1:0] == f_const_data[ 7: 6])
			##1 (i_dspi_dat[1:0] == f_const_data[ 5: 4])
			##1 (i_dspi_dat[1:0] == f_const_data[ 3: 2])
			##1 (i_dspi_dat[1:0] == f_const_data[ 1: 0]));

	assume property (@(posedge i_clk)
		disable iff ((i_reset)||(!i_wb_cyc))
		(i_wb_stb)&&(!o_wb_stall)&&(!i_wb_we)&&(!cfg_user_mode)
			&&(!o_dspi_cs_n)&&(i_wb_addr == f_const_addr)
		|=> (i_dspi_dat[1:0] == f_const_data[31:30])
			##1 (i_dspi_dat[1:0] == f_const_data[29:28])
			##1 (i_dspi_dat[1:0] == f_const_data[27:26])
			##1 (i_dspi_dat[1:0] == f_const_data[25:24])
			##1 (i_dspi_dat[1:0] == f_const_data[23:22])
			##1 (i_dspi_dat[1:0] == f_const_data[21:20])
			##1 (i_dspi_dat[1:0] == f_const_data[19:18])
			##1 (i_dspi_dat[1:0] == f_const_data[17:16])
			##1 (i_dspi_dat[1:0] == f_const_data[15:14])
			##1 (i_dspi_dat[1:0] == f_const_data[13:12])
			##1 (i_dspi_dat[1:0] == f_const_data[11:10])
			##1 (i_dspi_dat[1:0] == f_const_data[ 9: 8])
			##1 (i_dspi_dat[1:0] == f_const_data[ 7: 6])
			##1 (i_dspi_dat[1:0] == f_const_data[ 5: 4])
			##1 (i_dspi_dat[1:0] == f_const_data[ 3: 2])
			##1 (i_dspi_dat[1:0] == f_const_data[ 1: 0]));

	// Known data read, from idle
	assert property (@(posedge i_clk)
		disable iff ((i_reset)||(!i_wb_cyc))
		(i_wb_stb)&&(!o_wb_stall)&&(!i_wb_we)&&(!cfg_user_mode)
			&&(o_dspi_cs_n)&&(i_wb_addr == f_const_addr)
		|=> 1[*32]
		##1 (o_wb_ack)&&(o_wb_data == f_const_data));

	// Known pipelined data read
	assert property (@(posedge i_clk)
		disable iff ((i_reset)||(!i_wb_cyc))
		(i_wb_stb)&&(!o_wb_stall)&&(!i_wb_we)&&(!cfg_user_mode)
			&&(!o_dspi_cs_n)&&(i_wb_addr == f_const_addr)
		|=> 1[*16]
		##1 (o_wb_ack)&&(o_wb_data == f_const_data));

	// Configuration register read, high speed
	assert property (@(posedge i_clk)
		disable iff ((i_reset)||(!i_wb_cyc))
		(cfg_hs_read)
		##1 (((o_wb_stall)&&(!o_dspi_cs_n)&&(o_dspi_sck ==2'b01)
			&&(o_dspi_mod == `DUAL_READ)&&(!o_wb_ack)
			&&(cfg_user_mode)&&(cfg_user_speed)&&(!cfg_user_dir))
			throughout
			(clk_ctr == 6'd4)&&(i_dspi_dat == f_const_data[7:6])
			##1 (clk_ctr == 6'd3)&&(i_dspi_dat== f_const_data[5:4])
			##1 (clk_ctr == 6'd2)&&(i_dspi_dat== f_const_data[3:2])
			##1 (clk_ctr == 6'd1)&&(i_dspi_dat== f_const_data[1:0]))
		|=> ((o_wb_ack)||(!$past(pre_ack))||($past(!i_wb_cyc)))
			&&(o_cfg_data[7:0] == f_const_data[7:0])
			&&(cfg_user_mode)&&(cfg_user_speed));

	// Configuration register read, low speed
	assert property (@(posedge i_clk)
		disable iff ((i_reset)||(!i_wb_cyc))
		(cfg_ls_write)
		##1 (((o_wb_stall)&&(!o_dspi_cs_n)&&(o_dspi_sck ==2'b01)
			&&(o_dspi_mod == `NORMAL_SPI)&&(!o_wb_ack)
			&&(cfg_user_mode)&&(!cfg_user_speed))
			throughout
			(clk_ctr == 6'd8)&&(i_dspi_dat[1] == f_const_data[7])
			##1 (clk_ctr == 6'd7)&&(i_dspi_dat[1]==f_const_data[6])
			##1 (clk_ctr == 6'd6)&&(i_dspi_dat[1]==f_const_data[5])
			##1 (clk_ctr == 6'd5)&&(i_dspi_dat[1]==f_const_data[4])
			##1 (clk_ctr == 6'd4)&&(i_dspi_dat[1]==f_const_data[3])
			##1 (clk_ctr == 6'd3)&&(i_dspi_dat[1]==f_const_data[2])
			##1 (clk_ctr == 6'd2)&&(i_dspi_dat[1]==f_const_data[1])
			##1 (clk_ctr == 6'd1)&&(i_dspi_dat[1]==f_const_data[0]))
		|=> ((o_wb_ack)||(!$past(pre_ack))||($past(!i_wb_cyc)))
			&&(o_cfg_data[7:0] == f_const_data[7:0])
			&&(cfg_user_mode)&&(!cfg_user_speed));

`endif
	////////////////////////////////////////////////////////////////////////
	//
	// Cover Properties
	//
	////////////////////////////////////////////////////////////////////////
	//
	// Due to the way the chip starts up, requiring 32k+ maintenance clocks,
	// these cover statements are not likely to be hit
	always @(posedge i_clk)
		cover((o_wb_ack)&&(!cfg_user_mode));
	always @(posedge i_clk)
		cover((o_wb_ack)&&(!cfg_user_mode)&&(!$past(o_dspi_cs_n)));
	always @(posedge i_clk)
		cover((o_wb_ack)&&(!cfg_user_mode)&&(!o_dspi_cs_n));
	always @(posedge i_clk)
		cover((o_wb_ack)&&(cfg_user_mode)&&(cfg_user_speed));
	always @(posedge i_clk)
		cover((o_wb_ack)&&(cfg_user_mode)&&(!cfg_user_speed)&&(cfg_user_dir));
	always @(posedge i_clk)
		cover((o_wb_ack)&&(cfg_user_mode)&&(!cfg_user_speed)&&(!cfg_user_dir));

`endif
endmodule
// 				   (XPRS)	(PIPE)  (R/O)	(FULL)
//   Number of cells:                375	469	889	1248
//     FDRE                          117	140	231	 281
//     LUT1                           28	 30	 23	  23
//     LUT2                           50	 51	 83	 203
//     LUT3                           66	 66	 67	 166
//     LUT4                           10	 13	 29	  57
//     LUT5                           17	 20	 50	  95
//     LUT6                           17	 34	215	 256
//     MUXCY                          46	 67	 59	  59
//     MUXF7                           3	  4	 60	  31
//     MUXF8                           0	  1	  5	  10
//     XORCY                          21	 43	 67	  67


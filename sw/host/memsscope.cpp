////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	memsscope.cpp
//
// Project:	ArrowZip, a demonstration of the Arrow MAX1000 FPGA board
//
// Purpose:	This program decodes the bits in the debugging wires output
//		from the MEMS/Accelerometer device, making them available to be
//	read across the Wishbone bus via the Wishbone Scope device.  The result
//	is placed on the screen output, so you can see what is going on
//	internal to the device.
//		
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
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <strings.h>
#include <ctype.h>
#include <string.h>
#include <signal.h>
#include <assert.h>

#include "port.h"
#include "regdefs.h"
#include "scopecls.h"
#include "hexbus.h"

#define	WBSCOPE		R_MEMSSCOPE
#define	WBSCOPEDATA	R_MEMSSCOPED

#define	SCOPEBIT(VAL,B)	((val >> B)&1)

FPGA	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

class	MEMSSCOPE : public SCOPE {
	// While I put these in at one time, they really mess up other scopes,
	// since setting parameters based upon the debug word forces the decoder
	// to be non-constant, calling methods change, etc., etc., etc.
	//
	// int	m_oword[2], m_iword[2], m_p;
public:
	MEMSSCOPE(FPGA *fpga, unsigned addr, bool vecread)
		: SCOPE(fpga, addr, true, vecread) {};
	~MEMSSCOPE(void) {}
	virtual	void	decode(DEVBUS::BUSW val) const {
		int	ztimer, csn, sck, mosi, miso, stb, req, addr, retn,
			busy, done;

		busy   = SCOPEBIT(val, 30);
		ztimer = SCOPEBIT(val, 29);
		stb    = SCOPEBIT(val, 28);
		req    = SCOPEBIT(val, 27);
		addr   = (val >> 19)&0x0ff;
		retn   = (val >>  7)&0x0fff;
		done   = SCOPEBIT(val,  4);
		csn    = SCOPEBIT(val,  3);
		sck    = SCOPEBIT(val,  2);
		mosi   = SCOPEBIT(val,  1);
		miso   = SCOPEBIT(val,  0);
		printf("%8s%3s%4s%4s%5s%5s%4s%4s 0x%02x 0x?%03x %5s",
			(busy)?"BUSY -- ":"",
			(ztimer)?"CK":"",
			(csn)?"CSn":"",
			(sck)?"SCK":"",
			(mosi)?"MOSI":"",
			(miso)?"MISO":"",
			(stb)?"STB":"",
			(req)?"REQ":"",
			addr, retn,
			(done)?"DONE":"");
	}

	virtual	void define_traces(void) {
		register_trace("spi_busy",   1, 30);
		register_trace("ztimer",     1, 29);
		register_trace("stb_n_we",   1, 28);
		register_trace("spi_request",1, 27);
		register_trace("wb_addr",    8, 19);
		register_trace("wb_return", 12,  7);
		register_trace("o_int",      2,  5);
		register_trace("o_done",     1,  4);
		register_trace("o_cs_n",     1,  3);
		register_trace("o_sck",      1,  2);
		register_trace("o_mosi",     1,  1);
		register_trace("i_miso",     1,  0);
	}
};

int main(int argc, char **argv) {
#ifndef	R_MEMSSCOPE
	printf(
"This design was not built with a flash scope attached to the MEMSSCOPE\n"
"design component.\n"
"\n"
"To use this design, create and enable a flash, and the MEMSSCOPE scope from\n"
"that.  To do this, you'll need to adjust the flash configuration file\n"
"used by AutoFPGA found in the auto-data/ directory, and then include it\n"
"within the Makefile of the same directory.\n");
#else
	FPGAOPEN(m_fpga);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	MEMSSCOPE *scope = new MEMSSCOPE(m_fpga, WBSCOPE, true);
	scope->set_clkfreq_hz(CLKFREQHZ);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("mems.vcd");
	}
	delete	m_fpga;
#endif
}


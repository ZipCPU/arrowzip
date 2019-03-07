////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sdramscope.cpp
//
// Project:	ArrowZip, a demonstration of the Arrow MAX1000 FPGA board
//
// Purpose:	This program decodes the bits in the debugging wires output
//		from the SDRAM controller (the wbsdram module found in
//	wbsdram.v), and stored in the Wishbone Scope device.
//		
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2018-2019, Gisselquist Technology, LLC
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

#define	WBSCOPE		R_SDRAMSCOPE
#define	WBSCOPEDATA	R_SDRAMSCOPED

#define	SCOPEBIT(VAL,B)	((val >> B)&1)

FPGA	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

class	SDRAMSCOPE : public SCOPE {
	// While I put these in at one time, they really mess up other scopes,
	// since setting parameters based upon the debug word forces the decoder
	// to be non-constant, calling methods change, etc., etc., etc.
	//
	// int	m_oword[2], m_iword[2], m_p;
public:
	SDRAMSCOPE(FPGA *fpga, unsigned addr, bool vecread)
		: SCOPE(fpga, addr, true, vecread) {};
	~SDRAMSCOPE(void) {}
	virtual	void	decode(DEVBUS::BUSW val) const {
		int	cmd;

		printf("S(%x) ", (val>>27)&0x0f);
		if (val & 0x20000000)
			printf("W "); else printf("R ");
		printf("WB(%s%s%s%s%s",
			(val&0x80000000)?"CYC":"   ",
			(val&0x40000000)?"STB":"   ",
			(val&0x20000000)?"WE":"  ",
			(val&0x10000000)?"ACK":"   ",
			(val&0x08000000)?"STL":"   ");
			//
		if ((val&0xc8000000)==0xc0000000)
			printf("*");
		else
			printf(" ");
		printf(")-SD[%d%d%d%d,%d]",
			(val&0x04000000)?1:0,
			(val&0x02000000)?1:0,
			(val&0x01000000)?1:0,
			(val&0x00800000)?1:0,
			(val&0x00600000)>>21);
		cmd = (val >> 23)&0x0f;
		if (val&0x00100000)
			printf("<- ");
		else
			printf("-> ");
		printf("%s", (val&0x00080000)?"P":" "); // Pending
		printf("@%3x,", (val>>8)&0x07ff);
		/*
		printf(",%s%s%s%s%s", 
			(val&0x080)?"R":"-",
			(val&0x040)?"P":".",
			(val&0x020)?"P":".",
			(val&0x010)?"P":".",
			(val&0x008)?"P":".");
		printf("/%x%x%x", 
			(val>>2)&0x01,
			(val>>1)&0x01,
			(val&0x01));
		*/
		printf("/%02x ", val & 0x0ff);

		if (cmd & 0x8)
			printf("(inactive)");
		switch(cmd) {
			case 0x01: printf("Refresh"); break;
			case 0x02: printf("Precharge"); break;
			case 0x03: printf("Activate"); break;
			case 0x04: printf("Write"); break;
			case 0x05: printf("Read"); break;
			case 0x07: printf("NoOp"); break;
			default: break;
		}
	}

	virtual	void define_traces(void) {
		// register_trace(name, nbits, offset);
		register_trace("i_wb_cyc",    1, 31);
		register_trace("i_wb_stb",    1, 30);
		register_trace("i_wb_we",     1, 29);
		register_trace("o_wb_ack",    1, 28);
		register_trace("o_wb_stall",  1, 27);
		register_trace("o_ram_cs_n",  1, 26);
		register_trace("o_ram_ras_n", 1, 25);
		register_trace("o_ram_cas_n", 1, 24);
		register_trace("o_ram_we_n",  1, 23);
		register_trace("o_ram_bs",    2, 21);
		register_trace("o_ram_dmod",  1, 20);
		register_trace("r_pending",   1, 19);
		register_trace("trigger",     1, 18);
		register_trace("addr",       10,  8);
		register_trace("data",        8,  0);
	}
};

int main(int argc, char **argv) {
#ifndef	R_FLASHSCOPE
	printf(
"This design was not built with a flash scope attached to the WBSDRAM\n"
"design component.\n"
"\n"
"To use this design, create and enable the SDRAM, and the WBSDRAM scope from\n"
"that.  To do this, you'll need to adjust the sdramscope.txt configuration\n"
"file used by AutoFPGA found in the auto-data/ directory, and then include it\n"
"within the Makefile of the same directory.\n");
#else
	FPGAOPEN(m_fpga);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	SDRAMSCOPE *scope = new SDRAMSCOPE(m_fpga, WBSCOPE, false);
	scope->set_clkfreq_hz(CLKFREQHZ);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("sdram.vcd");
	}
	delete	m_fpga;
#endif
}


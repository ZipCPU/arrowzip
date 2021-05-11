////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sdramsim.h
// {{{
// Project:	ArrowZip, a demonstration of the Arrow MAX1000 FPGA board
//
// Purpose:	This module simulates an 16-bit SDRAM within a Verilator based
//		simulation environment.  It was originally written for the
//	xulalx25soc, but has now been modified for the ArrowZip project.
//
//	The simulator is designed to be called from the Verilator test harness
//	"tick" routine, or once per clock.  It returns the values from the
//	data lines, and asserts that the logic presented is done validly.
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
// }}}
#ifndef	SDRAMSIM_H

#define	NBANKS	4
#define	POWERED_UP_STATE	6
#define	CLK_RATE_HZ		100000000 // = 100 MHz = 100 * 10^6
#define	PWRUP_WAIT_CKS		((int)(.000200 * CLK_RATE_HZ))
#define	MAX_BANKOPEN_TIME	((int)(.000100 * CLK_RATE_HZ))
#define	MAX_REFRESH_TIME	((int)(.064 * CLK_RATE_HZ))
#define	SDRAM_QSZ		16

#define	LGSDRAMSZB	24
#define	SDRAMSZB	(1<<LGSDRAMSZB)

class	SDRAMSIM {
	int	m_pwrup;
	short	*m_mem;
	short	m_last_value, m_qmem[4];
	int	m_bank_status[NBANKS];
	int	m_bank_row[NBANKS];
	int	m_bank_open_time[NBANKS];
	unsigned	*m_refresh_time;
	int		m_refresh_loc, m_nrefresh;
	int	m_qloc, m_qdata[SDRAM_QSZ], m_qmask, m_wr_addr;
	int	m_clocks_till_idle;
	bool	m_next_wr;
	unsigned	m_fail;
	bool		m_debug;
public:
	SDRAMSIM(void) {
		m_mem = new short[SDRAMSZB/2]; // 32 MB, or 16 Mshorts

		m_refresh_time = new unsigned[(1<<13)];
		for(int i=0; i<m_nrefresh; i++)
			m_refresh_time[i] = 0;
		m_refresh_loc = 0;

		m_pwrup = 0;
		m_clocks_till_idle = 0;

		m_last_value = 0;
		m_clocks_till_idle = PWRUP_WAIT_CKS;
		m_wr_addr = 0;

		m_qloc  = 0;
		m_qmask = SDRAM_QSZ-1;

		m_next_wr = true;
		m_fail = 0;

		m_debug = false;
	}

	~SDRAMSIM(void) {
		delete m_mem;
	}

	short operator()(int clk, int cke,
			int cs_n, int ras_n, int cas_n, int we_n, int bs, 
				unsigned addr,
			int driv, short data, short dqm);
	int	pwrup(void) const { return m_pwrup; }

	void	load(unsigned addr, const char *data, size_t len) {
		short		*dp;
		const char	*sp = data;
		unsigned	base;

		assert((addr&1)==0);
		base = addr & (SDRAMSZB-1);
		assert((len&1)==0);
		assert(addr + len < SDRAMSZB);
		dp = &m_mem[(base>>1)];
		for(unsigned k=0; k<len/2; k++) {
			short	v;
			v = (sp[0]<<8)|(sp[1]&0x0ff);
			sp+=2;
			*dp++ = v;
		}
	}
};

#endif

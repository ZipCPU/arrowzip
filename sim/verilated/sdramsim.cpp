////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sdramsim.cpp
//
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
//
// Copyright (C) 2018, Gisselquist Technology, LLC
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
#include <assert.h>

#include "sdramsim.h"

short	SDRAMSIM::operator()(int clk, int cke, int cs_n, int ras_n, int cas_n, int we_n,
		int bs, unsigned addr, int driv, short data, short dqm) {
	short	result = 0;

	if (driv) // If the bus is going out, reads don't make sense ... but
		result = data; // read what we output anyway
	else if (!clk) // If the clock is zero, return our last value
		return m_last_value; // Always called w/clk=1, thus never here
	if (!cke) {
		fprintf(stderr, "SDRAM: This SDRAM simulation only supports CKE high!\n");
		fprintf(stderr, "\tCKE   = %d\n", cke);
		fprintf(stderr, "\tCS_n  = %d\n", cs_n);
		fprintf(stderr, "\tRAS_n = %d\n", ras_n);
		fprintf(stderr, "\tCAS_n = %d\n", cas_n);
		fprintf(stderr, "\tWE_n  = %d\n", we_n);
		assert(cke);
	}

	if (m_pwrup < POWERED_UP_STATE) {
		assert(dqm == 3);
		if (m_clocks_till_idle > 0)
			m_clocks_till_idle--;
		if (m_pwrup == 0) {
			assert((cs_n)&&(ras_n)&&(cas_n)&&(we_n)&&(dqm==3));
			if (m_clocks_till_idle == 0) {
				m_pwrup++;
				if (m_debug) printf("SDRAM: Successful power up wait, moving to state #1\n");
			}
		} else if (m_pwrup == 1) {
			if ((!cs_n)&&(!ras_n)&&(cas_n)&&(!we_n)&&(addr&0x0400)) {
				// Wait until a precharge all banks command
				m_pwrup++;
				if (m_debug) printf("SDRAM: Successful precharge command, moving to state #2\n");
				m_clocks_till_idle = 8;
			}
		} else if (m_pwrup == 2) {
			static	bool	mode_is_set = false;
			static	int	refresh_cycles = 0;

			if ((!cs_n)&&(!ras_n)&&(!cas_n)&&(!we_n)) {
				assert(!mode_is_set);
				assert((refresh_cycles == 0)||(refresh_cycles == 8));
				// mode set
				if (m_debug) printf("SDRAM: Mode set: %08x\n", addr);
				assert(addr == 0x021);
				mode_is_set = true;
			}

			if ((!cs_n)&&(!ras_n)&&(!cas_n)&&(we_n)) {
				refresh_cycles++;
				assert(refresh_cycles <= 8);

				if (m_debug) printf("SDRAM: #%d refresh cycles\n", refresh_cycles);
			}

			if (mode_is_set && refresh_cycles >= 8) {
				const int tRSC = 2;
				m_pwrup++;
				for(int i=0; i<m_nrefresh; i++)
					m_refresh_time[i] = MAX_REFRESH_TIME;
				m_clocks_till_idle=tRSC;

				if (m_debug) printf("SDRAM: Moving to power up state 3\n");
			}
		} else if (m_pwrup == 3) {
			assert(cs_n);
			if (m_clocks_till_idle == 0) {
				m_pwrup = POWERED_UP_STATE;
				m_clocks_till_idle = 0;
				if (m_debug) printf("SDRAM: Successful settup!  SDRAM switching to operational\n");
			} else if (m_clocks_till_idle == 1) {
				;
			} else assert(0 && "SDRAM: Should never get here!");
		} else if (m_pwrup == 4) {
			if ((!cs_n)&&(!ras_n)&&(!cas_n)&&(we_n)) {
				if (m_clocks_till_idle == 0) {
					m_pwrup = POWERED_UP_STATE;
					m_clocks_till_idle = 0;

					for(int i=0; i<m_nrefresh; i++)
						m_refresh_time[i] = MAX_REFRESH_TIME;
				}
			} else {
				assert(0);
			}
		}
		m_next_wr = false;
	} else { // In operation ...
		for(int i=0; i<m_nrefresh; i++)
			m_refresh_time[i]--;
		if (m_refresh_time[m_refresh_loc] < 0) {
			assert(0 && "Failed refresh requirement");
		} for(int i=0; i<NBANKS; i++) {
			m_bank_status[i] >>= 1;
			if (m_bank_status[i]&2)
				m_bank_status[i] |= 4;
			if (m_bank_status[i]&1) { // Bank is open
				m_bank_open_time[i] --;
				if (m_bank_open_time[i] < 0) {
					assert(0 && "Bank held open too long");
				}
			}
		}

		if (m_clocks_till_idle)
			m_clocks_till_idle--;

		if (m_fail > 0) {
			m_fail--;
			if (m_fail == 0) {
				fprintf(stderr, "Failing on schedule\n");
				exit(-3);
			}
		}

		if ((m_clocks_till_idle > 0)&&(m_next_wr)) {
			if (m_debug) printf("SDRAM[%08x] <= %04x (BM=%d)\n", m_wr_addr, data & 0x0ffff, (dqm&3)^3);
			int	waddr = m_wr_addr++, memval;
			memval = m_mem[waddr];
			if ((dqm&3)==0)
				memval = data;
			else if ((dqm&3)==3)
				;
			else if ((dqm&2)==0)
				memval = (memval & 0x000ff) | (data & 0x0ff00);
			else // if ((dqm&1)==0)
				memval = (memval & 0x0ff00) | (data & 0x000ff);
			m_mem[waddr] = memval;
			result = data;
			m_next_wr = false;
		}
		m_qloc = (m_qloc + 1)&m_qmask;
		result = (driv)?data:m_qdata[(m_qloc)&m_qmask];
		m_qdata[(m_qloc)&m_qmask] = 0;

		// if (result != 0)
			// printf("%d RESULT[%3d] = %04x\n", clk, m_qloc, result&0x0ffff);

		if ((!cs_n)&&(!ras_n)&&(!cas_n)&&(we_n)) {
			// Auto-refresh command
			m_refresh_time[m_refresh_loc] = MAX_REFRESH_TIME;
			m_refresh_loc++;
			if (m_refresh_loc >= m_nrefresh)
				m_refresh_loc = 0;
			assert((m_bank_status[0]&6) == 0);
			assert((m_bank_status[1]&6) == 0);
			assert((m_bank_status[2]&6) == 0);
			assert((m_bank_status[3]&6) == 0);
		} else if ((!cs_n)&&(!ras_n)&&(cas_n)&&(!we_n)) {
			if (addr&0x0400) {
				// Bank/Precharge All CMD
				for(int i=0; i<NBANKS; i++)
					m_bank_status[i] &= 0x03;
			} else {
				// Precharge/close single bank
				assert(0 == (bs & (~3))); // Assert w/in bounds
				m_bank_status[bs] &= 0x03; // Close the bank

				if (m_debug) printf("SDRAM: Precharging bank %d\n", bs);
			}
		} else if ((!cs_n)&&(!ras_n)&&(cas_n)&&(we_n)) {
			if (m_debug) printf("SDRAM: Activating bank %d\n", bs);
			// Activate a bank!
			if (0 != (bs & (~3))) {
				m_fail = 2;
				fprintf(stderr, "ERR: Activating a bank w/ more than 2 bits\n");
				// assert(0 == (bs & (~3))); // Assert w/in bounds
			} else if (m_bank_status[bs] != 0) {
				fprintf(stderr, "ERR: Status of bank [bs=%d] = %d != 0\n",
					bs, m_bank_status[bs]);
				m_fail = 4;
				// assert(m_bank_status[bs]==0); // Assert bank was closed
			}
			m_bank_status[bs] |= 4;
			m_bank_open_time[bs] = MAX_BANKOPEN_TIME;
			m_bank_row[bs] = addr;
		} else if ((!cs_n)&&(ras_n)&&(!cas_n)) {
			if (m_debug) printf("SDRAM: R/W Op\n");
			if (!we_n) {
				// Initiate a write
				assert(0 == (bs & (~3))); // Assert w/in bounds
				assert(m_bank_status[bs]&1); // Assert bank is open

				m_wr_addr = m_bank_row[bs];
				m_wr_addr <<= 2;
				m_wr_addr |= bs;
				m_wr_addr <<= 9;
				m_wr_addr |= (addr & 0x01ff);

				assert(driv);
				if (m_debug) printf("SDRAM: SDRAM[%08x] <= %04x\n", m_wr_addr, data & 0x0ffff);
				m_mem[m_wr_addr++] = data;
				m_clocks_till_idle = 2;
				m_next_wr = true;

				if (addr & 0x0400) { // Auto precharge
					m_bank_status[bs] &= 3;
					m_bank_open_time[bs] = MAX_BANKOPEN_TIME;
				}
			} else { // Initiate a read
				assert(0 == (bs & (~3))); // Assert w/in bounds
				assert(m_bank_status[bs]&1); // Assert bank is open

				unsigned	rd_addr;

				rd_addr = m_bank_row[bs] & 0x01fff;
				rd_addr <<= 2;
				rd_addr |= bs;
				rd_addr <<= 9;
				rd_addr |= (addr & 0x01ff);

				assert(!driv);
				if (m_debug) printf("SDRAM.Q[%2d] %04x <= SDRAM[%08x]\n",
					(m_qloc+3)&m_qmask,
					m_mem[rd_addr] & 0x0ffff, rd_addr);
				m_qdata[(m_qloc+3)&m_qmask] = m_mem[rd_addr++];
				if (m_debug) printf("SDRAM.Q[%2d] %04x <= SDRAM[%08x]\n",
					(m_qloc+4)&m_qmask,
					m_mem[rd_addr] & 0x0ffff, rd_addr);
				m_qdata[(m_qloc+4)&m_qmask] = m_mem[rd_addr++];
				m_clocks_till_idle = 2;

				if (addr & 0x0400) { // Auto precharge
					m_bank_status[bs] &= 3;
					m_bank_open_time[bs] = MAX_BANKOPEN_TIME;
				}
			}
		} else if (cs_n) {
			// Chips not asserted, DESELECT CMD equivalent of a NOOP
		} else if ((ras_n)&&(cas_n)&&(we_n)) {
			// NOOP command
		} else {
			fprintf(stderr, "Unrecognized memory command!\n");
			fprintf(stderr, "\tCS_n  = %d\n", cs_n);
			fprintf(stderr, "\tRAS_n = %d\n", ras_n);
			fprintf(stderr, "\tCAS_n = %d\n", cas_n);
			fprintf(stderr, "\tWE_n  = %d\n", we_n);
			assert(0 && "Unrecognizned command");
		}
	}

	return result & 0x0ffff;
}



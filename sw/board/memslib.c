////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	memslib.c
// {{{
// Project:	ArrowZip, a demonstration of the Arrow MAX1000 FPGA board
//
// Purpose:	Provide high level access to a variety of LIS3DH (Mems)
//		device registers.
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
//  {{{
//		http://www.gnu.org/licenses/gpl.html
//
////////////////////////////////////////////////////////////////////////////////
//
// }}}
#include "board.h"

void	mems_wait(void) {
	while(_mems->rd[0] & 0x80000000)
		;
}

int	mems_read8(int addr) {
	addr &= 0x3f;
	mems_wait();
	_mems->rd[addr] = 0;
	mems_wait();
	return _mems->rd[addr] & 0x0ff;
}

int	mems_read16(int addr) {
	addr &= 0x3f;
	mems_wait();
	_mems->rd[64+addr] = 0;
	mems_wait();
	return _mems->rd[addr] & 0x0ffff;
}

void	mems_write8(int addr, int val) {
	addr &= 0x3f;
	mems_wait();
	_mems->wr[addr] = val;
}

void	mems_write16(int addr, int val) {
	addr &= 0x3f;
	mems_wait();
	_mems->wr[64+addr] = val;
}

void	mems_accel_init(void) {
	mems_write8(R_MEMSCTRL0, 0x90);
	mems_write8(R_MEMSCTRL1, 0x57);
	mems_write8(R_MEMSCTRL2, 0x00);
	mems_write8(R_MEMSCTRL3, 0x00);
	mems_write8(R_MEMSCTRL4, 0x88);
	mems_write8(R_MEMSCTRL5, 0x00);
	mems_write8(R_MEMSCTRL6, 0x00);
	mems_write8(R_MEMSREF,   0x00);
	mems_write8(R_MEMSFIFOC, 0x00);
	mems_write8(R_MEMSINT1C, 0x00);
	mems_write8(R_MEMSINT2C, 0x00);
	mems_write8(R_MEMSCKCFG, 0x00);
}

int	mems_data_ready(void) {
	int	st;

	st = mems_read8(R_MEMSSTAT);
	if (st & 4)
		return 1;
}

void	mems_readxyz(int *xyz) {
	xyz[0] = mems_read16(R_MEMSX);
	xyz[1] = mems_read16(R_MEMSY);
	xyz[2] = mems_read16(R_MEMSZ);
}

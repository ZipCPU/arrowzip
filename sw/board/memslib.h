////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	memslib.h
//
// Project:	ArrowZip, a demonstration of the Arrow MAX1000 FPGA board
//
// Purpose:	Provide high level access to a variety of LIS3DH (Mems)
//		device registers.
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
#ifndef	MEMSLIB_H
#define	MEMSLIB_H

extern	void	mems_wait(void);
extern	int	mems_read8(int addr);
extern	int	mems_read16(int addr);
extern	void	mems_write8(int addr, int val);
extern	void	mems_write16(int addr, int val);
extern	void	mems_accel_init(void);
extern	int	mems_data_ready(void);
extern	void	mems_readxyz(int *);

#endif

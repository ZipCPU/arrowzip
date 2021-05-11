////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	lvldemo.c
// {{{
// Project:	ArrowZip, a demonstration of the Arrow MAX1000 FPGA board
//
// Purpose:	
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
#include <stdio.h>
#include <stdlib.h>
#include <board.h>
#include "memslib.h"

int	main(int argc, char **argv) {
	printf("LVL Demo\n");
	mems_accel_init();

	while(1) {
		int	xyz[3], sumsqi, divi;

		while(!mems_data_ready())
			;
		mems_readxyz(xyz);

		// Sign extend our values
		for(int i=0; i<3; i++)
			if (xyz[i] & 0x1000)
				xyz[i] |= ~0x0fff;

		// Calculate the sum of the square values
		sumsqi = xyz[0]*xyz[0] + xyz[1]*xyz[1] + xyz[2]*xyz[2];
		divi = xyz[1] * xyz[1] * 128 / (sumsqi);

		printf("%5d, %5d, %5d -> %11d / %23d\n", xyz[0], xyz[1], xyz[2],
			divi, sumsqi);
	}
}

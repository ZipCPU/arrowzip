////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	memtest.c
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
// Copyright (C) 2019-2021, Gisselquist Technology, LLC
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
#include "zipcpu.h"
#include "board.h"

#define	SCOPE_DELAY	4

asm("\t.section\t.start\n"
	"\t.global\t_start\n"
	"\t.type\t_start,@function\n"
"_start:\n"
	"\tCLR\tR0\n"
	"\tCLR\tR1\n"
	"\tCLR\tR2\n"
	"\tCLR\tR3\n"
	"\tCLR\tR4\n"
	"\tCLR\tR5\n"
	"\tCLR\tR6\n"
	"\tCLR\tR7\n"
	"\tCLR\tR8\n"
	"\tCLR\tR9\n"
	"\tCLR\tR10\n"
	"\tCLR\tR11\n"
	"\tCLR\tR12\n"
	"\tLDI\t_top_of_stack,SP\n"
	"\tCLR\tCC\n"
	"\tJSR\tentry\n"
"busy_failure:\n"
	"\tBUSY\n"
	"\t.section\t.text");

#define	STEP(F,T)	asm volatile("LSR 1,%0\n\tXOR.C %1,%0" : "+r"(F) : "r"(T))

#define	FAIL		asm("TRAP")

void	runtest(void) {
	int	counts = 0;
	const	int	TAPS = 0x0485b5;
	int	*const mem = (int *)_sdram;
	int	*const end = (int *)(&_sdram[sizeof(_sdram)]);
	char	*const endc= &_sdram[sizeof(_sdram)];

#ifdef	_BOARD_HAS_SPIO
	// Clear any/all LED's
	*_spio = 0x0ff00;
#endif

#ifdef	_BOARD_HAS_ZIPSCOPE
	_zipscope->s_ctrl = SCOPE_DELAY;
#endif
#ifdef	_BOARD_HAS_SDRAMSCOPE
	_sdramdbg->s_ctrl = SCOPE_DELAY;
#endif

	while(1) {
		if (++counts == 0)
			counts = 1;

#ifdef	_BOARD_HAS_SPIO
		// Clear the bottom 4 LED's
		*_spio = 0x0f00;
#endif


		//
		//
		// #1, sequential access, filled with LRS
		//
		//
		{
			int	*mptr = mem;
			unsigned fill;

			fill = counts;
			while(mptr < end) {
				STEP(fill,TAPS);
				*mptr++ = fill;
			}

			fill = counts;
			mptr = mem;
			while(mptr < end) {
				STEP(fill,TAPS);
				if (*mptr != (int)fill)
					FAIL;
				mptr++;
			}
		}

#ifdef	_BOARD_HAS_SPIO
		// First test done, set the bottom LED
		*_spio = 0x0f01;
#endif

		//
		//
		// #2, sequential access, read/write 3x at a time
		//
		//
		if (1) {
			int	*mptr = mem;
			unsigned fill;

			fill = counts + 4;
			while(mptr+3 < end) {
				register unsigned a, b, c;


				STEP(fill, TAPS);
				a = fill;

				STEP(fill, TAPS);
				b = fill;

				STEP(fill, TAPS);
				c = fill;

				// asm("SW %1,%0" : "=m"(mptr[0]) : "r"(a));
				// asm("SW %1,%0" : "=m"(mptr[1]) : "r"(b));
				// asm("SW %1,%0" : "=m"(mptr[2]) : "r"(c));

				mptr[0] = a;
				mptr[1] = b;
				mptr[2] = c;

				mptr += 3;

// fill = 5, a = 0x0485b7, b = 0x06c76e, c = 0x0363b7
			}

			mptr = mem;
			fill = counts+4;
			while(mptr+3 < end) {
				register unsigned a, b, c;

				// asm("LW %1,%0" : "=r"(a) : "m"(mptr[0]));
				// asm("LW %1,%0" : "=r"(b) : "m"(mptr[1]));
				// asm("LW %1,%0" : "=r"(c) : "m"(mptr[2]));

				a = mptr[0];
				b = mptr[1];
				c = mptr[2];
// fill = 5, a = 0x06c76f, b = 0x06c76f

				STEP(fill, TAPS);
				if (a != (int)fill)
					FAIL;

				STEP(fill, TAPS);
				if (b != (int)fill)
					FAIL;

				STEP(fill, TAPS);
				if (c != (int)fill)
					FAIL;

				mptr+=3;
			}
		}

#ifdef	_BOARD_HAS_SPIO
		// Second test done, set the LEDs to reflect that
		*_spio = 0x0f03;
#endif


		//
		//
		// #3, sequential access, read/write 3x characters at a time
		//
		//
		if (1) {
			char	*mcptr;
			unsigned fill;

			mcptr = _sdram;
			fill = counts + 19;

			while(mcptr+3 < endc) {
				register char a, b, c;

				asm("LSR 1,%0\n\tXOR.C %1,%0" : "+r"(fill) : "r"(TAPS));
				a = fill & 0x0ff;

				asm("LSR 1,%0\n\tXOR.C %1,%0" : "+r"(fill) : "r"(TAPS));
				b = fill & 0x0ff;

				asm("LSR 1,%0\n\tXOR.C %1,%0" : "+r"(fill) : "r"(TAPS));
				c = fill & 0x0ff;

				mcptr[0] = a;
				mcptr[1] = b;
				mcptr[2] = c;

				// asm("SB %1,%0" : "=m"(mcptr[0]) : "r"(a));
				// asm("SB %1,%0" : "=m"(mcptr[1]) : "r"(b));
				// asm("SB %1,%0" : "=m"(mcptr[2]) : "r"(c));

				mcptr += 3;
			}

			mcptr = _sdram;
			fill = counts+19;
			while(mcptr+3 < endc) {
				register unsigned a, b, c;

				// asm("LB  (%1),%0" : "=r"(a) : "r"(mcptr));
				// asm("LB 1(%1),%0" : "=r"(b) : "r"(mcptr));
				// asm("LB 2(%1),%0" : "=r"(c) : "r"(mcptr));

				a = mcptr[0];
				b = mcptr[1];
				c = mcptr[2];

				asm("LSR 1,%0\n\tXOR.C %1,%0" : "+r"(fill) : "r"(TAPS));
				if (((a ^ (int)fill)&0x0ff)!=0)
					FAIL;

				asm("LSR 1,%0\n\tXOR.C %1,%0" : "+r"(fill) : "r"(TAPS));
				if (((b ^ (int)fill)&0x0ff)!=0)
					FAIL;

				asm("LSR 1,%0\n\tXOR.C %1,%0" : "+r"(fill) : "r"(TAPS));
				if (((c ^ (int)fill)&0x0ff)!=0)
					FAIL;

				mcptr+=3;
			}
		}

#ifdef	_BOARD_HAS_SPIO
		// Third test done
		*_spio = 0x0f07;
#endif


		//
		//
		// #4, random access, read/write one word at a time
		//
		//
		{
			int	*mptr = mem;
			unsigned afill, dfill, amsk;

			afill = counts;
			dfill = counts + 23;
			amsk  = (sizeof(_sdram)>>2) - 1;
			do {
				asm("LSR 1,%0\n\tXOR.C %1,%0" : "+r"(afill) : "r"(TAPS));
				asm("LSR 1,%0\n\tXOR.C %1,%0" : "+r"(dfill) : "r"(TAPS));
				if ((afill&(~amsk)) == 0)
					mptr[afill&amsk] = dfill;
			} while(afill != counts);

			afill = counts;
			dfill = counts + 23;
			do {
				asm("LSR 1,%0\n\tXOR.C %1,%0" : "+r"(afill) : "r"(TAPS));
				asm("LSR 1,%0\n\tXOR.C %1,%0" : "+r"(dfill) : "r"(TAPS));
				if ((afill & (~amsk)) == 0) {
					if (mptr[afill&amsk] != (int)dfill)
					FAIL;
				}
			} while(afill != counts);
		}
#ifdef	_BOARD_HAS_SPIO
		// Fourth test done
		*_spio = 0x0f0f;

		// Toggle bit 5 (0x10) as well--since we just finished another
		// round.  This way the toggling bit will be the indication
		// that the memory controller has been successful.
		if (*_spio&0x010)
			*_spio = 0x1000;
		else
			*_spio = 0x1010;
#endif

	}

failure:
	FAIL;
}

void	entry(void) {
	unsigned zero = 0;
	unsigned	usp[512];

	asm("MOV %0,uR0" : : "r"(zero));
	asm(
	"\tMOV uR0,uR1\n"
	"\tMOV uR0,uR2\n"
	"\tMOV uR0,uR3\n"
	"\tMOV uR0,uR4\n"
	"\tMOV uR0,uR5\n"
	"\tMOV uR0,uR6\n"
	"\tMOV uR0,uR7\n"
	"\tMOV uR0,uR8\n"
	"\tMOV uR0,uR9\n"
	"\tMOV uR0,uR10\n"
	"\tMOV uR0,uR11\n"
	"\tMOV uR0,uR12\n"
	);

	asm("MOV %0,uSP" : : "r"(&usp[511]));
	asm("MOV %0,uPC" : : "r"(runtest));
	zip_rtu();
	*_spio = 0x0ffff;
#ifdef	_BOARD_HAS_ZIPSCOPE
	_zipscope->s_ctrl = WBSCOPE_TRIGGER|SCOPE_DELAY;
#endif
#ifdef	_BOARD_HAS_SDRAMSCOPE
	_sdramdbg->s_ctrl = WBSCOPE_TRIGGER|SCOPE_DELAY;
#endif
	asm("NSTR \"MEMTEST FAILURE!\"\n");
	asm("NDUMP\n");
	asm("NEXIT\n");
	zip_halt();
}


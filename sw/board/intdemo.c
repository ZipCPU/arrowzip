////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	intdemo.c
// {{{
// Project:	ArrowZip, a demonstration of the Arrow MAX1000 FPGA board
//
// Purpose:	Demonstrate multi-tasking with interrupts on the ZipCPU, using
//		two outgoiing LEDs, toggled at different rates.  We'll do this
//	by running four programs:
//
//	1. One that toggles LED[0] at 1Hz
//	2. One that toggles LED[2] at 2Hz, synchronous with the first
//	3. One that toggles LED[4] at 3Hz, synchronous with the first
//	4. One that toggles LED[6] at 5Hz, synchronous with the first
//
//	The supervisor processor will enable LED's 1,3,5, and 7 any time
//	it is enabled.
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
#include <stdint.h>
#include "zipcpu.h"
#include "board.h"

extern	char	_top_of_heap[0];
unsigned _heap = (unsigned)_top_of_heap;

int	milliseconds = 0;
typedef	void	(*voidfn)();

void	toggleled(int led_bits, int rate) {
	while(1) {
		int	ms = milliseconds, led;
		ms = ms * (rate * 2);
		led = (ms / 1000) & 1;

		if (led)
			*_spio = (led_bits<<8);
		else
			*_spio = (led_bits << 8) | (led_bits);
	}
}

void	one_hz(void) {
	toggleled(1, 1);
}


void	two_hz(void) {
	toggleled(4, 2);
}

void	three_hz(void) {
	toggleled(16, 3);
}

void	five_hz(void) {
	toggleled(64, 5);
}

#define	NTASKS	4

typedef	struct {
	int	r[16];
} task_context;

void	*ugly_malloc(unsigned nbytes) {
	void	*r = (void *)_heap;
	_heap = _heap + ((nbytes+3)/4);
	return 	r;
}

int	*new_stack_ptr(unsigned nbytes) {
	int	*ptr = (int *)ugly_malloc(nbytes);

	ptr = &ptr[((nbytes+3)>>2)-1];
	return ptr;
}

void	panic(void) {
	while(1) {
		int	v;
		v = *_pwrcount >> 28;
		v &= 1;
		if (v)
			*_spio = 0x0ffff;
		else
			*_spio = 0x0ff00;
	}
}

void	memzero(void *p, int v, unsigned cnt) {
	char	*cp = p;
	for(int i=0; i<cnt; i++)
		*cp++ = v;
}

void	entry(void) {
	unsigned	heartbeats = 0;
	task_context	tasks[NTASKS];
	task_context	*current;

	memzero(tasks, 0, sizeof(task_context)* NTASKS);
	// Give each task a stack, and a program counter
	for(int i=0; i<NTASKS; i++)
		tasks[i].r[13] = (unsigned)new_stack_ptr(256);
	tasks[0].r[15] = (unsigned)((voidfn)one_hz);
	tasks[1].r[15] = (unsigned)((voidfn)two_hz);
	tasks[2].r[15] = (unsigned)((voidfn)three_hz);
	tasks[3].r[15] = (unsigned)((voidfn)five_hz);

	current = &tasks[0];
	zip_restore_context(current->r);
	*_bustimer = (0x80000000)|((CLKFREQHZ-1)/1000);
	// Enable interrupts, and our interrupt in particular
	*_buspic = 0x80008000 | BUSPIC_BUSTIMER | (BUSPIC_BUSTIMER<<16);

	while(1) {
		int	picv;

		*_spio = 0xaa00;
		heartbeats++;
		zip_rtu();
		*_spio = 0xaaaa;
		if (zip_ucc() & (CC_EXCEPTION))
			panic();
		picv = *_buspic;
		if (picv & BUSPIC_BUSTIMER) {
			// Timer interrupt triggered
			milliseconds = milliseconds+1;
			if (milliseconds >= 1000)
				milliseconds = 0;
		}

		// Reset the interrupt
		*_buspic = BUSPIC_BUSTIMER;

		// Swap tasks
		zip_save_context(current->r);
		for(int i=0; i<NTASKS; i++) {
			if (current == &tasks[i]) {
				current = &tasks[(i+1 >= NTASKS)?0:i+1];
				break;
			}
		}
		zip_restore_context(current->r);
	}
}

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
	"\tMOV\tbusy_failure(PC),R0\n"
	"\tBRA\tentry\n"
"busy_failure:\n"
	"\tBUSY\n"
	"\t.section\t.text");

int	main(int argc, char **argv) {
	entry();
}


// To build this:
//	zip-gcc -O3 -Wall -Wextra -nostdlib -fno-builtin -T xula.ld -Wl,-Map,cputest.map cputest.cpp -o cputest
//	zip-objdump -D cputest > cputest.txt
//

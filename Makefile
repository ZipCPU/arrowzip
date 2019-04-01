################################################################################
##
## Filename:	Makefile
##
## Project:	ArrowZip, a demonstration of the Arrow MAX1000 FPGA board
##
## Purpose:	A master project makefile.  It tries to build all targets
##		within the project, mostly by directing subdirectory makes.
##
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
##
## Copyright (C) 2015-2019, Gisselquist Technology, LLC
##
## This program is free software (firmware): you can redistribute it and/or
## modify it under the terms of  the GNU General Public License as published
## by the Free Software Foundation, either version 3 of the License, or (at
## your option) any later version.
##
## This program is distributed in the hope that it will be useful, but WITHOUT
## ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
## for more details.
##
## You should have received a copy of the GNU General Public License along
## with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
## target there if the PDF file isn't present.)  If not, see
## <http://www.gnu.org/licenses/> for a copy.
##
## License:	GPL, v3, as defined and found on www.gnu.org,
##		http://www.gnu.org/licenses/gpl.html
##
##
################################################################################
##
##
.PHONY: all
all:	check-install archive rtl sim sw
#
# Could also depend upon load, if desired, but not necessary
BENCH := # `find bench -name Makefile` `find bench -name "*.cpp"` `find bench -name "*.h"`
SIM   := `find sim -name Makefile` `find sim -name "*.cpp"` `find sim -name "*.h"` `find sim -name "*.c"`
RTL   := `find rtl -name "*.v"` `find rtl -name Makefile`
NOTES := `find . -name "*.md"` `find . -name "*.html"`
SW    := `find sw -name "*.cpp"` `find sw -name "*.c"`	\
	`find sw -name "*.h"`	`find sw -name "*.sh"`	\
	`find sw -name "*.py"`	`find sw -name "*.pl"`	\
	`find sw -name "*.png"`	`find sw -name Makefile`
DEVSW := `find sw/board -name "*.cpp"` `find sw/board -name "*.h"` \
	`find sw/board -name Makefile`
PROJ  :=
BIN  := # `find xilinx -name "*.bit"`
AUTODATA := `find auto-data -name "*.txt"`
CONSTRAINTS := `find . -name "*.xdc"`
YYMMDD:=`date +%Y%m%d`
SUBMAKE:= $(MAKE) --no-print-directory -C
SOCDIR := rtl/arrowzip
SIMDIR := sim/verilated
ZIPSW  := sw/board
LIBXSVG:= ../../ftdi/libxsvf/xsvftool-ft232h

#
#
# Check that we have all the programs available to us that we need
#
#
.PHONY: check-install
check-install: check-perl check-verilator check-zip-gcc check-gpp

.PHONY: check-perl
	$(call checkif-installed,perl,)

.PHONY: check-autofpga
check-autofpga:
	$(call checkif-installed,autofpga,-V)

.PHONY: check-verilator
check-verilator:
	$(call checkif-installed,verilator,-V)

.PHONY: check-zip-gcc
check-zip-gcc:
	$(call checkif-installed,zip-gcc,-v)

.PHONY: check-gpp
check-gpp:
	$(call checkif-installed,g++,-v)

#
#
#
# Now that we know that all of our required components exist, we can build
# things
#
#
#
# Create a datestamp file, so that we can check for the build-date when the
# project was put together.
#
.PHONY: datestamp
datestamp: check-perl
	perl mkdatev.pl > $(YYMMDD)-build.v
	cd $(SOCDIR); cp ../../$(YYMMDD)-build.v builddate.v

#
#
# Make a tar archive of this file, as a poor mans version of source code control
# (Sorry ... I've been burned too many times by files I've wiped away ...)
#
ARCHIVEFILES := $(BENCH) $(SW) $(RTL) $(SIM) $(NOTES) $(PROJ) $(BIN) $(CONSTRAINTS) $(AUTODATA) README.md
.PHONY: archive
archive:
	tar --transform s,^,$(YYMMDD)-arrowzip/, -chjf $(YYMMDD)-arrowzip.tjz $(ARCHIVEFILES)

#
#
# Build our main (and toplevel) Verilog files via autofpga
#
.PHONY: autodata datestamp
autodata: check-autofpga datestamp
	$(SUBMAKE) auto-data
	$(MAKE) --no-print-directory --directory=auto-data
	$(call copyif-changed,auto-data/toplevel.v,$(SOCDIR)/toplevel.v)
	$(call copyif-changed,auto-data/main.v,$(SOCDIR)/main.v)
	$(call copyif-changed,auto-data/regdefs.h,sw/host/regdefs.h)
	$(call copyif-changed,auto-data/regdefs.cpp,sw/host/regdefs.cpp)
	$(call copyif-changed,auto-data/board.h,sw/zlib/board.h)
	$(call copyif-changed,auto-data/board.ld,$(ZIPSW)/board.ld)
	$(call copyif-changed,auto-data/flash.ld,$(ZIPSW)/flash.ld)
	$(call copyif-changed,auto-data/bkram.ld,$(ZIPSW)/bkram.ld)
	$(call copyif-changed,auto-data/sdram.ld,$(ZIPSW)/sdram.ld)
	$(call copyif-changed,auto-data/rtl.make.inc,$(SOCDIR)/make.inc)
	$(call copyif-changed,auto-data/testb.h,$(SIMDIR)/testb.h)
	$(call copyif-changed,auto-data/main_tb.cpp,$(SIMDIR)/main_tb.cpp)
	$(call copyif-changed,auto-data/iscachable.v,$(SOCDIR)/cpu/iscachable.v)

#
#
# Verify that the rtl has no bugs in it, while also creating a Verilator
# simulation class library that we can then use for simulation
#
.PHONY: verilated
verilated: check-verilator
	+@$(SUBMAKE) rtl/simple
	+@$(SUBMAKE) $(SOCDIR)

.PHONY: rtl
rtl: verilated

VENDOR=0x0403
PRODUCT=0x6010
DEVICE=-D i:$(VENDOR):$(PRODUCT)
load:
	echo "(sudo) $(LIBXSVG) $(DEVICE) -C A -s ../quartus/toplevel.svf"
#
#
# Build a simulation of this entire design
#
.PHONY: sim
sim: rtl check-gpp
	+@$(SUBMAKE) $(SIMDIR)

#
#
# A master target to build all of the support software
#
.PHONY: sw
sw: sw-host sw-zlib sw-board

#
#
# Build the host support software
#
.PHONY: sw-host
sw-host:
	$(SUBMAKE) sw/host

#
#
# Build the hardware specific newlib library
#
.PHONY: sw-zlib
sw-zlib: check-zip-gcc
	+@$(SUBMAKE) sw/zlib

#
#
# Build the board software.  This may (or may not) use the software library
#
.PHONY: sw-board
sw-board: sw-zlib check-zip-gcc
	+@$(SUBMAKE) $(ZIPSW)

#
#
# Run "Hello World", and ... see if this all works
#
.PHONY: hello
hello: sim sw
	$(SIMDIR)/main_tb $(ZIPSW)/hello

.PHONY: cputest
cputest: sim sw
	$(SIMDIR)/main_tb $(ZIPSW)/cputest

# .PHONY: test
# test: hello

#
#
# Copy a file from the auto-data directory that had been created by
# autofpga, into the directory structure where it might be used.
#
define	copyif-changed
	@bash -c 'cmp $(1) $(2); if [[ $$? != 0 ]]; then echo "Copying $(1) to $(2)"; cp $(1) $(2); fi'
endef

#
#
# Check if the given program is installed
#
define	checkif-installed
	@bash -c '$(1) $(2) < /dev/null >& /dev/null; if [[ $$? != 0 ]]; then echo "Program not found: $(1)"; exit -1; fi'
endef


.PHONY: clean
clean:
	+$(SUBMAKE) auto-data     clean
	+$(SUBMAKE) $(SIMDIR)     clean
	+$(SUBMAKE) rtl/simple    clean
	+$(SUBMAKE) $(SOCDIR)     clean
	+$(SUBMAKE) sw/zlib       clean
	+$(SUBMAKE) $(ZIPSW)      clean
	+$(SUBMAKE) sw/host       clean

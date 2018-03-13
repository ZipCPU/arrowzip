################################################################################
##
## Filename:	bench/formal/Makefile
##
## Project:	ArrowZip, a demonstration of the Arrow MAX1000 FPGA board
##
## Purpose:	To direct the formal verification of the sources associated
##		with the ArrowZip project.
##
## Targets:	The default target, all, tests all of the components defined
##		within this module.
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
##
## Copyright (C) 2017, Gisselquist Technology, LLC
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
################################################################################
##
##
TESTS := mems
.PHONY: $(TESTS)
all: $(TESTS)
RTL := ../../rtl/arrowzip
SMTBMC  := yosys-smtbmc
# SOLVER  := -s z3
SOLVER  := -s yices
BMCARGS := --presat $(SOLVER)
INDARGS := $(SOLVER) -i

MEMS   := mems
FLASH  := dualflexpress
#
WBSLAVE  := fwb_slave.v

$(MEMS).smt2: $(RTL)/$(MEMS).v $(WBSLAVE)
	yosys -ql $(MEMS).yslog -s $(MEMS).ys

$(FLASH).smt2: $(RTL)/$(FLASH).v $(WBSLAVE)
	yosys -ql $(FLASH).yslog -s $(FLASH).ys

.PHONY: $(MEMS)
$(MEMS) : $(MEMS).check
$(MEMS).check: $(MEMS).smt2
	rm -f $@
	$(SMTBMC)    $(BMCARGS) -t 106 --dump-vcd $(MEMS).vcd $(MEMS).smt2
	$(SMTBMC)    $(INDARGS) -t 104 --dump-vcd $(MEMS).vcd $(MEMS).smt2
	$(SMTBMC) -g $(BMCARGS) -t 112 --dump-vcd $(MEMS).vcd $(MEMS).smt2
	touch $@


.PHONY: $(FLASH)
$(FLASH) : $(FLASH).check
$(FLASH).check: $(FLASH).smt2
	rm -f $@
	$(SMTBMC)    $(BMCARGS) -t 106 --dump-vcd $(FLASH).vcd $(FLASH).smt2
	$(SMTBMC)    $(INDARGS) -t 104 --dump-vcd $(FLASH).vcd $(FLASH).smt2
	$(SMTBMC) -c $(BMCARGS) -t 300 --dump-vcd $(FLASH)%.vcd $(FLASH).smt2
	touch $@

.PHONY: clean
clean:
	rm -f  $(MEMS).yslog   $(MEMS).smt2    $(MEMS)*.vcd   $(MEMS).check
	rm -f *.check

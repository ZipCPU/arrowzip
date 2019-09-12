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
## Copyright (C) 2017-2019, Gisselquist Technology, LLC
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
#
WBSLAVE  := fwb_slave.v

$(MEMS): $(MEMS)_prflil/PASS $(MEMS)_prfbig/PASS $(MEMS)_cvr/PASS
$(MEMS)_prflil/PASS: $(MEMS).sby $(RTL)/$(MEMS).v $(WBSLAVE)
	sby -f $(MEMS).sby prflil
$(MEMS)_prfbig/PASS: $(MEMS).sby $(RTL)/$(MEMS).v $(WBSLAVE)
	sby -f $(MEMS).sby prfbig
$(MEMS)_cvr/PASS: $(MEMS).sby $(RTL)/$(MEMS).v $(WBSLAVE)
	sby -f $(MEMS).sby cvr

.PHONY: clean
clean:
	rm -f  $(MEMS)_*/

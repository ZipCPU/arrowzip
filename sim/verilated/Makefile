################################################################################
##
## Filename:	Makefile
## {{{
## Project:	ArrowZip, a demonstration of the Arrow MAX1000 FPGA board
##
## Purpose:	To coordinate the build of a cycle accurate, Verilator based,
##		simulation of the main module.  Access to the simulation is
##	provided via the same software commands that will access the board, save
##	that the parameters are a touch different.  (See the access software for
##	more information ...)
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
## }}}
## Copyright (C) 2015-2021, Gisselquist Technology, LLC
## {{{
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
## }}}
## License:	GPL, v3, as defined and found on www.gnu.org,
## {{{
##		http://www.gnu.org/licenses/gpl.html
##
################################################################################
##
## }}}
.PHONY: all
# Make certain the "all" target is the first and therefore the default target
all:
CXX	:= g++
OBJDIR	:= obj-pc
RTLD	:= ../../rtl/arrowzip
VOBJDR	:= $(RTLD)/obj_dir
ifneq ($(VERILATOR_ROOT),)
VERILATOR:=$(VERILATOR_ROOT)/bin/verilator
else
VERILATOR_ROOT ?= $(shell bash -c 'verilator -V|grep VERILATOR_ROOT | head -1 | sed -e " s/^.*=\s*//"')
endif
export	$(VERILATOR)
VROOT   := $(VERILATOR_ROOT)
VDEFS   := $(shell ./vversion.sh)
VINCD   := $(VROOT)/include
VINC	:= -I$(VINCD) -I$(VINCD)/vltstd -I$(VOBJDR)
INCS	:= -I. -I../../sw/host -I$(RTLD) $(VINC)
CFLAGS	:= -Og -g -Wall $(INCS) $(VDEFS)
#
# A list of our sources and headers
#
SIMSOURCES:= flashsim.cpp sdramsim.cpp dbluartsim.cpp zipelf.cpp byteswap.cpp
SIMOBJECTS:= $(addprefix $(OBJDIR)/,$(subst .cpp,.o,$(SIMSOURCES)))
SIMHEADERS:= $(foreach header,$(subst .cpp,.h,$(SIMSOURCES)),$(wildcard $(header)))
VOBJS   := $(OBJDIR)/verilated.o $(OBJDIR)/verilated_vcd_c.o
SIMOBJ := $(subst .cpp,.o,$(SIMSRCS))
SIMOBJS:= $(addprefix $(OBJDIR)/,$(SIMOBJ)) $(VOBJS)

SOURCES := $(SIMSOURCES) main_tb.cpp automaster_tb.cpp
HEADERS := $(foreach header,$(subst .cpp,.h,$(SOURCES)),$(wildcard $(header)))
#
PROGRAMS := main_tb
# Now the return to the "all" target, and fill in some details
all:	$(PROGRAMS)

$(OBJDIR)/%.o: %.cpp
	$(mk-objdir)
	$(CXX) $(CFLAGS) $(VDEFS) $(INCS) -c $< -o $@

$(OBJDIR)/%.o: $(VINCD)/%.cpp
	$(mk-objdir)
	$(CXX) $(CFLAGS) $(INCS) -c $< -o $@

$(OBJDIR)/main_tb.o: automaster_tb.cpp
	$(CXX) $(CFLAGS) $(INCS) -c $< -o $@

VMAIN := $(VOBJDR)/Vmain__ALL.a
MAINOBJS := $(OBJDIR)/main_tb.o
main_tb: $(MAINOBJS) $(SIMOBJECTS) $(VOBJS) $(VMAIN)
	$(CXX) $(VDEFS) $(CFLAGS) $^ $(VOBJDR)/Vmain__ALL.a -lelf -o $@

#
#
# The "test" target, running hello world
#
.PHONY: test
test:
	./main_tb -d ../../sw/board/hello

#
# The "clean" target, removing any and all remaining build products
#
.PHONY: clean
clean:
	rm -f *.vcd
	rm -f $(PROGRAMS)
	rm -rf $(OBJDIR)/

#
# The "depends" target, to know what files things depend upon.  The depends
# file itself is kept in $(OBJDIR)/depends.txt
#
define build-depends
	$(mk-objdir)
	@echo "Building dependency file"
	@$(CXX) $(VDEFS) $(CFLAGS) $(INCS) -MM $(SOURCES) > $(OBJDIR)/xdepends.txt
	@sed -e 's/^.*.o: /$(OBJDIR)\/&/' < $(OBJDIR)/xdepends.txt > $(OBJDIR)/depends.txt
	@rm $(OBJDIR)/xdepends.txt
endef

.PHONY: depends
depends: tags
	$(build-depends)

$(OBJDIR)/depends.txt: depends

#
define	mk-objdir
	@bash -c "if [ ! -e $(OBJDIR) ]; then mkdir -p $(OBJDIR); fi"
endef


#
# The "tags" target
#
tags:	$(SOURCES) $(HEADERS)
	@echo "Generating tags"
	@ctags $(SOURCES) $(HEADERS)


ifneq ($(MAKECMDGOALS),clean)
-include $(OBJDIR)/depends.txt
endif

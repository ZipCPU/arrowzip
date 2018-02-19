## ArrowZip

This design is currently a work in progress.  The goal is to place a
[ZipCPU](http://zipcpu.com/about/zipcpu.html) onto a
[$30 Max1000 FPGA](http://zipcpu.com/blog/2017/12/16/max1k.html),
as sold by [Arrow](https://www.arrow.com) and
[Trenz Electronics](https://www.trenz-electronic.de).

If all goes well, this will include access to ...

- The on-board SDRAM.  This includes not only the
  [Verilog code](rtl/arrowzip/wbsdram.v) to access this SDRAM, but also a
  [simulation component](sim/verilated/sdramsim.cpp) for the SDRAM, as well
  as an [AutoFPGA](https://github.com/ZipCPU/autofpga)
  [script](auto-data/sdram.txt)
  to add (or remove) the SDRAM from this build.

- A dual-I/O flash, running in both XIP (Execute in Place) mode as well as
  a debug-bus configuration override.  As with the SDRAM, this will include
  not only the [Verilog code](rtl/arrowzip/dualflexpress.v), but also a
  simulation component and an [AutoFPGA](https://github.com/ZipCPU/autofpga)
  [script](auto-data/flexpress.txt)
  to add (or remove) the flash from this build.

- The on-board MEMS motion sensor.

At present, the design builds but it has yet to be tested within even a
simulation environment--much less on the actual hardware.  However, it has
been built using Quartus, so it is known that the current design will not only
fit but also meet timing--just not whether or not it will work.  (Presumably
it will not.)

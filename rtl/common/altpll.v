(* blackbox *)
module altpll (
	input	[1:0]	inclk,
	output	[4:0]	clk,
	output		locked,
	output	activeclock,
	input		areset,
	output	clkbad,
	input	[5:0]	clkena,
	output	clkloss,
	input		clkswitch,
	input		configupdate,
	output	enable0,
	output	enable1,
	output	extclk,
	input [3:0]	extclkena,
	input		fbin,
	output	fbmimicbidir,
	output	fbout,
	output	fref,
	output	icdrclk,
	input		pfdena,
	input	[3:0]	phasecounterselect,
	output	phasedone,
	input		phasestep,
	input		phaseupdown,
	input		pllena,
	input		scanaclr,
	input		scanclk,
	input		scanclkena,
	input		scandata,
	output	scandataout,
	output	scandone,
	input		scanread,
	input		scanwrite,
	output	sclkout0,
	output	sclkout1,
	output	vcooverrange,
	output	vcounderrange
	);
parameter bandwidth_type = "AUTO";
parameter clk0_divide_by = 3;
parameter	clk0_duty_cycle = 50;
parameter	clk0_multiply_by = 25;
parameter	clk0_phase_shift = "0";
parameter	compensate_clock = "CLK0";
parameter	inclk0_input_frequency = 83333;
parameter	intended_device_family = "MAX 10";
parameter	lpm_hint = "CBX_MODULE_PREFIX=ippll";
parameter	lpm_type = "altpll";
parameter	operation_mode = "NORMAL";
parameter	pll_type = "AUTO";
parameter	port_activeclock = "PORT_UNUSED";
parameter	port_areset = "PORT_UNUSED";
parameter	port_clkbad0 = "PORT_UNUSED";
parameter	port_clkbad1 = "PORT_UNUSED";
parameter	port_clkloss = "PORT_UNUSED";
parameter	port_clkswitch = "PORT_UNUSED";
parameter	port_configupdate = "PORT_UNUSED";
parameter	port_fbin = "PORT_UNUSED";
parameter	port_inclk0 = "PORT_USED";
parameter	port_inclk1 = "PORT_UNUSED";
parameter	port_locked = "PORT_USED";
parameter	port_pfdena = "PORT_UNUSED";
parameter	port_phasecounterselect = "PORT_UNUSED";
parameter	port_phasedone = "PORT_UNUSED";
parameter	port_phasestep = "PORT_UNUSED";
parameter	port_phaseupdown = "PORT_UNUSED";
parameter	port_pllena = "PORT_UNUSED";
parameter	port_scanaclr = "PORT_UNUSED";
parameter	port_scanclk = "PORT_UNUSED";
parameter	port_scanclkena = "PORT_UNUSED";
parameter	port_scandata = "PORT_UNUSED";
parameter	port_scandataout = "PORT_UNUSED";
parameter	port_scandone = "PORT_UNUSED";
parameter	port_scanread = "PORT_UNUSED";
parameter	port_scanwrite = "PORT_UNUSED";
parameter	port_clk0 = "PORT_USED";
parameter	port_clk1 = "PORT_UNUSED";
parameter	port_clk2 = "PORT_UNUSED";
parameter	port_clk3 = "PORT_UNUSED";
parameter	port_clk4 = "PORT_UNUSED";
parameter	port_clk5 = "PORT_UNUSED";
parameter	port_clkena0 = "PORT_UNUSED";
parameter	port_clkena1 = "PORT_UNUSED";
parameter	port_clkena2 = "PORT_UNUSED";
parameter	port_clkena3 = "PORT_UNUSED";
parameter	port_clkena4 = "PORT_UNUSED";
parameter	port_clkena5 = "PORT_UNUSED";
parameter	port_extclk0 = "PORT_UNUSED";
parameter	port_extclk1 = "PORT_UNUSED";
parameter	port_extclk2 = "PORT_UNUSED";
parameter	port_extclk3 = "PORT_UNUSED";
parameter	self_reset_on_loss_lock = "OFF";
parameter	width_clock = 5;
endmodule


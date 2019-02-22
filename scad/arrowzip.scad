include <GT.scad>
include <zipcpu.scad>
include <max1klogo.scad>
	
module	arrowcase(cap = 0) {
	//
	// Measurements
	raw_board_thickness =  1.3;
	bx_component_thickness = 2*(3.2-raw_board_thickness)
					+raw_board_thickness + 2.5;
	raw_board_width     = 26.0;
	raw_board_length    = 62.0;
	//
	bx_board_thickness     = raw_board_thickness + 0.7;
	bx_board_width         = raw_board_width  + 0.7;
	bx_board_length        = raw_board_length + 0.7;
	bx_clear_board_edge    =  7.0;
	//
	usb_height = 4.2-raw_board_thickness + 0.5;
	usb_width  = 7.6  + 0.5;
	usb_depth  = 5.25 + 0.5;

	////////////////////////////
	//
	// USB plug dimensions
	//
	// This isn't the actual metal USB size.  That's fixed by the
	// standard.  This is the size of the plastic that surrounds
	// that plug.
	//
	// First USB plug dimensions
	// usb_plug_width = 10.1 + 1.5;
	usb_plug_height=  6.8 + 1.5;

	// Second plug dimensions
	usb_plug_width = 11.8 + 1.5;
	// usb_plug_height=  5.9 + 1.5;

	// Second plug dimensions
	// usb_plug_width = 9.0 + 1.5;
	usb_plug_height=  7.6 + 1.5;

	////////////
	//
	standoff_height       = 10;
	standoff_flat_to_flat = 4.5;
	//
	screw_diameter= 2.5;
	screw_length  = 4.1;
	screw_head_diameter = 5.5+0.6;
	screw_head_height   = 1.5;
	//
	// Derived measurements
	// standoff_radius = standoff_flat_to_flat / sqrt(2.0);
	// Because this is an "inside" standoff, it the radius is measured
	// to the flats, not the corners
	standoff_radius = standoff_flat_to_flat;
	//
	// My choices
	tolerance = 0.1;
	bx_edge_thickness = standoff_flat_to_flat + 3;
	bx_component_width = bx_board_width-bx_clear_board_edge;
	chamber_height = bx_component_thickness;
	exwidth  = bx_board_width    + 2*bx_edge_thickness;
	exlength = bx_board_length   + 2*bx_edge_thickness;
	exheight = chamber_height    + 2*bx_edge_thickness;
	
	inx = bx_edge_thickness + tolerance/2;
	iny = bx_edge_thickness + tolerance/2;
	inz = bx_edge_thickness;
	bottom_of_board = inz + chamber_height/2-bx_board_thickness/2;
	
	module raw_case() {
		cube([exwidth, exlength, exheight]);
	}
	
	module	rounded_case() {
		rad = bx_edge_thickness;
		tol = tolerance;
		union() {
			difference() {
				raw_case();
				//
				translate([-tol,-tol,-tol])
					cube([rad+tolerance,exlength+2*tol,
						rad+tol]);
				translate([exwidth-rad,-tolerance,-tolerance])
					cube([rad+tol,exlength+2*tol,
						rad+tol]);
				translate([-tolerance,exlength-rad,-tol])
					cube([exwidth+2*tol,rad+tol,
						rad+tol]);
				translate([-tol,exlength-rad,-tol])
					cube([rad+tol,rad+tol,
						exheight+2*tol]);
				translate([exwidth-rad,exlength-rad,-tol])
					cube([rad+tol,rad+tol,
						exheight+2*tol]);
				// Top side
				translate([-tol,-tol,exheight-rad])
					cube([rad+tol,exlength+2*tol,
						rad+2*tol]);
				translate([exwidth-rad,-tol,exheight-rad])
					cube([rad+tol,exlength+2*tol,
						rad+2*tol]);
				translate([-tol,exlength-rad,exheight-rad])
					cube([exwidth+2*tol,rad+2*tol,
						rad+2*tol]);
				// Front side
				translate([-tol,-tol,-tol])
					cube([exwidth+2*tol,rad+tol,
						rad+tol]);
				translate([-tol,-tol,exheight-rad])
					cube([exwidth+2*tol,rad+tol,
						rad+tol]);
				translate([-tol,-tol,-tol])
					cube([rad+tol,rad+tol,
						exheight+2*tol]);
				translate([exwidth-rad,-tol,-tol])
					cube([rad+tol,rad+tol,
						exheight+2*tol]);
			}
	
			// The corners
			translate([rad,exlength-rad,rad])
				sphere(rad);
			translate([exwidth-rad,exlength-rad,rad])
				sphere(rad);
			translate([rad,exlength-rad,exheight-rad])
				sphere(rad);
			translate([exwidth-rad,exlength-rad,exheight-rad])
				sphere(rad);
			// Front corners
			translate([rad,rad,rad])
				sphere(rad);
			translate([exwidth-rad,rad,rad])
				sphere(rad);
			translate([rad,rad,exheight-rad])
				sphere(rad);
			translate([exwidth-rad,rad,exheight-rad])
				sphere(rad);
	
	
	
			// The sides
			translate([rad,rad,rad]) rotate([-90,0,0])
				cylinder(h=exlength-2*rad,r=rad);
			translate([exwidth-rad,rad,rad]) rotate([-90,0,0])
				cylinder(h=exlength-2*rad,r=rad);
			translate([rad,exlength-rad,rad]) rotate([0,90,0])
				cylinder(h=exwidth-2*rad,r=rad);
			// And on the top
			translate([rad,rad,exheight-rad]) rotate([-90,0,0])
				cylinder(h=exlength-2*rad,r=rad);
			translate([exwidth-rad,rad,exheight-rad]) rotate([-90,0,0])
				cylinder(h=exlength-2*rad,r=rad);
			translate([rad,exlength-rad,exheight-rad]) rotate([0,90,0])
				cylinder(h=exwidth-2*rad,r=rad);
			// Vertical supports
			translate([rad,exlength-rad,rad])
				cylinder(h=exheight-2*rad,r=rad);
			translate([exwidth-rad,exlength-rad,rad])
				cylinder(h=exheight-2*rad,r=rad);
			// The front face
			translate([rad,rad,rad]) rotate([0,90,0])
				cylinder(h=exwidth-2*rad,r=rad);
			translate([rad,rad,exheight-rad]) rotate([0,90,0])
				cylinder(h=exwidth-2*rad,r=rad);
			translate([exwidth-rad,rad,rad])
				cylinder(h=exheight-2*rad,r=rad);
			translate([rad,rad,rad])
				cylinder(h=exheight-2*rad,r=rad);
		}
	}
	
	module	inside_chamber() {
		bw = bx_board_width;
		ch = chamber_height;
		cw = bx_component_width;
		// tol=tolerance;
		tol=0.1;
		spare_end_width = 22;
		btnw = 1;

		union() {
			// Room for the bare board
			//
			translate([inx-tol/2, iny-tol/2,
					inz+(ch-bx_board_thickness-tol)/2])
				cube([bx_board_width+tol,
					bx_board_length+tol,
					bx_board_thickness+tol]);
	
			// Room for the electronics around the board
			translate([inx+(bw-cw-tol)/2, iny-tol/2+bx_clear_board_edge/2,
					inz-tol/2])
				cube([cw + tol,
					bx_board_length-bx_clear_board_edge/2+tol,
					chamber_height+tol]);

			// Room for the electronics near the end
			translate([inx-btnw+tol/2, iny-tol/2,
					inz-tol/2])
				cube([bx_board_width+btnw*2+tol,
					spare_end_width+tol,
					chamber_height+tol]);
		}
	}
	
	module	board() {
		color("green") {
			translate([inx, iny,
				bottom_of_board])
				cube([bx_board_width, bx_board_length, bx_board_thickness]);
		}
	}
	
	module	embossGT() {
		s = 0.25;
		depth = 1.5;
		union() {
			translate([exwidth+gtlogo_h*s/2-depth,
				exlength-2*s*gtlogo_l-bx_edge_thickness-1.5,
				gtlogo_l*s/2+bx_edge_thickness]) {
			rotate([0,0,90]) { rotate([90,0,0]) { scale([s,s,s]) {
				translate([-gtlogo_w*s,-gtlogo_l*s,-gtlogo_h*s]);
						GTlogo(); }
			}}}
	
			translate([-gtlogo_h*s/2+depth,
				gtlogo_l*s+bx_edge_thickness + 3,
				gtlogo_w*s/2+bx_edge_thickness]) {
			rotate([0,0,-90]) { rotate([90,0,0]) { scale([s,s,s]) {
	
				translate([-gtlogo_w*s,-gtlogo_l*s,-gtlogo_h*s])
					GTlogo(); }
			}}}
		}
	}
	
	module	embossZip() {
		s = 1.0;
		depth = 1.5;
		union() {
			translate([exwidth/2,
				exlength/2,
				exheight+zlogoh/2-depth])
			{
			rotate([0,0,90]) scale([s,s,1]) {
				translate([-zlogow/2,(zlogob-zlogol)/2,-zlogoh/2])
						zipcpulogo(); }
			}
		}
	}

	module	embossMax1k(depth) {
		s = 1.2;
		sw = s * max1klogo_w;
		sl = s * max1klogo_l;
		sh = max1klogo_l;
		depth = 1.5;
		union() {
			translate([exwidth/2,
				exlength/2,
				-max1klogo_h/2+depth])
			{
			rotate([0,180,90]) scale([s,s,1]) {
				translate([-max1klogo_w/2,-max1klogo_l/2,-max1klogo_h/2])
						max1klogo(); }
			}
		}
	}

	module	standoff_holes() {
		tol = tolerance;
		rad = standoff_flat_to_flat;
		shp = standoff_height+tol;
		// Inset = (distance from edge) + rad/2
		// Inset = 2mm + rad
		inset = 1.5+rad;
		translate([inset, iny+standoff_height+tol, inset])
			rotate([90,0,0])
				cylinder(h=shp,r=standoff_radius,$fn=6);
		translate([exwidth-inset, iny+standoff_height+tol, inset])
			rotate([90,0,0])
				cylinder(h=shp,r=standoff_radius,$fn=6);
		translate([inset, iny+standoff_height+tol, exheight-inset])
			rotate([90,0,0])
				cylinder(h=shp,r=standoff_radius,$fn=6);
		translate([exwidth-inset, iny+standoff_height+tol,	
				 exheight-inset])
			rotate([90,0,0])
				cylinder(h=shp,r=standoff_radius,$fn=6);
	
		// clean things up a ... touch
		/*
		translate([rad, iny-tol, rad*3/4])
			cube([exwidth-2*rad,standoff_height+tol,
				exheight-2*rad*3/4]);
		*/
		/*
		translate([rad, iny-tol, rad])
			cube([exwidth-2*rad,standoff_height+tol,
				exheight-rad*2.0]);
		*/
	}
	
	module	screw_holes() {
		tol = tolerance;
		rad = standoff_flat_to_flat;
		inset = 1.5+rad;
		srad= (screw_diameter)/2;
		sch= iny+standoff_height/2;
		headr = (screw_head_diameter+0.8+tol)/2;

		// The four screw holes themselves
		translate([inset, sch-tol, inset]) rotate([90,0,0])
			cylinder(h=sch,r=srad);
		translate([exwidth-inset, sch-tol, inset]) rotate([90,0,0])
			cylinder(h=sch,r=srad);
		translate([inset, sch-tol, exheight-inset]) rotate([90,0,0])
			cylinder(h=sch,r=srad);
		translate([exwidth-inset, sch-tol, exheight-inset]) rotate([90,0,0])
			cylinder(h=sch,r=srad);
	
		// Make sure we have space for the heads!
		translate([0,iny-screw_length/2,0]) {
			translate([inset, 0, inset]) rotate([90,0,0])
				cylinder(h=standoff_height,r=headr);
			translate([inset, 0, exheight-inset]) rotate([90,0,0])
				cylinder(h=standoff_height,r=headr);
			translate([exwidth-inset, 0, inset]) rotate([90,0,0])
				cylinder(h=standoff_height,r=headr);
			translate([exwidth-inset, 0, exheight-inset]) rotate([90,0,0])
				cylinder(h=standoff_height,r=headr);
		}
	}
	
	module	front_face(cap = 0) {
		// clearance spacing, spx
		spx = (cap > 0) ? -0.5 : 0.5;

		// The first block must be larger than the rest
		// This is the block that holds the majority of the front face,
		// to include the curved sides.
		translate([-tolerance, -tolerance, -tolerance])
			cube([exwidth+2*tolerance,
				iny + tolerance,exheight + 2*tolerance]);
	
		rad = bx_edge_thickness*3/4;
		plug_top_width  = exwidth -2.00*rad+1+spx/2;
		plug_mid_width  = exwidth -1.25*rad+1+spx/2;
		plug_top_height = exheight-     rad-1+spx/2;
		plug_mid_height = exheight-2.05*rad-1+spx/2;

		/*
		* OLD VERSION
		*
		//
		color("red") {
		translate([(exwidth-plug_top_width)/2, -tolerance,
				(exheight-plug_top_height)/2])
			cube([plug_top_width, iny + tolerance + rad,
				plug_top_height]);
		//
		translate([(exwidth-plug_mid_width)/2,
				-tolerance,
				(exheight-plug_mid_height)/2])
			cube([plug_mid_width, iny + tolerance + rad,
				plug_mid_height]);
		}
		*/

		translate([0,(iny+tolerance+rad),0]) {
				rotate([90,0,0]) {
					linear_extrude(iny+tolerance+rad) {
			polygon(points=[
				[(exwidth-plug_top_width)/2,
					(exheight-plug_top_height)/2],
			//
				[(exwidth-plug_mid_width)/2,
				  (exheight-plug_mid_height)/2],
				[(exwidth-plug_mid_width)/2,
				  (exheight-plug_mid_height)/2
					+plug_mid_height],
			//
				[(exwidth-plug_top_width)/2,
				  (exheight-plug_top_height)/2
					+plug_top_height],
				[(exwidth-plug_top_width)/2
					+plug_top_width,
				  (exheight-plug_top_height)/2
					+plug_top_height],
			//
				[(exwidth-plug_mid_width)/2
					+plug_mid_width,
				  (exheight-plug_mid_height)/2
					+plug_mid_height],
				[(exwidth-plug_mid_width)/2
					+plug_mid_width,
				  (exheight-plug_mid_height)/2],
			//
				[(exwidth-plug_top_width)/2
					+plug_top_width,
				  (exheight-plug_top_height)/2],
/*
				//
*/
				]);
		}}}
	}
	
	module	usb_hole() {
		port_l = usb_width;
		port_h = usb_height;
		port_x = exwidth/2-port_l/2;
		tob = bottom_of_board+bx_board_thickness;
		port_y = tob;
		//
		plug_l = usb_plug_width;
		plug_h = usb_plug_height;
		plug_x = (exwidth-plug_l)/2;
		plug_z = (tob+port_h/2)-plug_h/2;
		//
		tol = tolerance+0.1;
		//
		// The USB connector on the board
		translate([port_x-tol/2, -2*tol, tob-tol/2])
			cube([port_l+tol, 4*tol+iny+usb_depth, port_h+tol]);
		//
		// The space for the USB plug
		translate([plug_x-tol/2, 0,
				plug_z-tol/2])
			cube([plug_l+tol, iny+tol, plug_h+tol]);
	}
	
	module	assembled() {
		difference() {
			rounded_case();
			color("white") {
				inside_chamber(); }
			color("red")  { embossGT();  }
			color("blue") { embossZip(); }
			color("green"){ embossMax1k();  }
			// front_face();
			standoff_holes();
			screw_holes();
			usb_hole();
		}
	}

	module	front_face_supports() {
		port_l = usb_width -2;
		port_h = usb_height -2;
		port_x = exwidth/2-port_l/2;
		tob = bottom_of_board+bx_board_thickness + 1;
		port_y = tob;
		//
		plug_l = usb_plug_width -2;
		plug_h = usb_plug_height -2;
		plug_x = (exwidth-plug_l)/2;
		plug_z = (tob+port_h/2)-plug_h/2;
		//
		tol = tolerance+0.1;
		//
		// The USB connector on the board
		translate([port_x-tol/2, 0, bottom_of_board+bx_board_thickness ])
			cube([port_l+tol, iny+usb_depth-2, port_h+1+tol]);
		//
		// The space for the USB plug
		translate([plug_x-tol/2, 0,
				plug_z-tol/2])
			cube([plug_l+tol, iny-2, plug_h+tol]);

		//
		// Space to protect the screw holes
		//
		tol = tolerance;
		rad = standoff_flat_to_flat;
		inset = 1.5+rad;
		sln = iny-screw_length/2-1;
		srad= (screw_diameter)/2;
		sch= iny+standoff_height/2;
		headr = (screw_head_diameter+0.8+tol)/2;

		// Create some supports for the head holes, so they print well
		translate([0,0,0]) {
			translate([inset, sln, inset]) rotate([90,0,0])
				cylinder(h=sln,r=headr-1);
			translate([inset, sln, exheight-inset]) rotate([90,0,0])
				cylinder(h=sln,r=headr-1);
			translate([exwidth-inset, sln, inset]) rotate([90,0,0])
				cylinder(h=sln,r=headr-1);
			translate([exwidth-inset, sln, exheight-inset]) rotate([90,0,0])
				cylinder(h=sln,r=headr-1);
		}
	}

	module	whole_design(cap = -1) {
		// cap =  1  for the top
		// cap =  0  for the base
		// cap = -1 for the whole assembled design
		//
		union() {
			if (cap < 0) {
				assembled();
			} else if (cap > 0) {
				intersection() {
					assembled();
					front_face(cap);
				}
			} else {
				difference() {
					assembled();
					front_face(cap);
			 	}
			}
			// board();
			// color("red") { embossGT(); }
			// color("blue") { embossZip(); }
		}
	
		/*
		rad = bx_edge_thickness;
		translate([rad, iny-tolerance, rad])
			cube([exwidth-2*rad,standoff_height+tolerance,
				exheight-rad*2.0]);
		*/
	}
	
	if (cap > 3) {
		front_face(1);
	} else if (cap > 2) {
		difference() {
			translate([exwidth+20, 35, exlength-1]) {
				rotate([ -90, 0, 90 ])
					whole_design(0);
			}

			translate([-tolerance/2,-tolerance/2,exheight*3/4]) {
				cube([100,100,2*exheight]);
			}
		}
	} else if (cap > 1) {
		difference() {
			whole_design(-1);

			translate([-tolerance/2, -tolerance/2, exheight/2+1]) {
				cube([exwidth+tolerance, exlength+tolerance,
					exheight/2+tolerance]);
			}
		}
	} else if (cap > 0) {
		whole_design(cap);
		//
		front_face_supports();
	} else {
		translate([0, 0, exlength]) {
			rotate([ -90, 0, 0 ])
				whole_design(cap);
		}
	}
}

tol = 0.5;
if (0) {
	translate([0,0,-4]) {
		difference() {
			union() {
				arrowcase(2);
				translate([10,0,0]) {
					arrowcase(3);
				}
			}
	
			translate([0,0,-20-tol/2]) {
				cube([80,80,24+tol/2]);
			}
		}
	}
	translate([35, 0, 0 ]) {
		rotate([90, 0, 90]) {
			arrowcase(1);
		}
	}
} else {
	arrowcase(0);

	translate([0, 50, 0 ]) {
		rotate([90, 0, 0]) {
			arrowcase(1);
		}
	}
	/*
	translate([0, 0, 55 ]) {
		rotate([270, 0, 0]) {
			arrowcase(1);
		}
	}
	*/
}

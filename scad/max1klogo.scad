module	max1klogo() {
	module	max1k() {
		linear_extrude(height=5) {
			union() {
				// M
				polygon(points=[
					[0,0],
					[1,0],
					[7,6],
					[7,4],
					[8,4],
					[4,0],
					[5,0],
					[12,7],
					[11,7],
					[8,5],
					[8,7],
					[7,7] ]);
				// A
				polygon(points=[
					[7,0],
					[8,0],
					[14,6],
					[17,6],
					[15,4],
					[13,4],
					[12,3],
					[14,3],
					[11,0],
					[12,0],
					[18,6],
					[18,7],
					[14,7],
					]);
				// X
				polygon(points=[
					[14,0],
					[15,0],
					[18,3],
					[18,4] ]);
				polygon(points=[
					[17,0],
					[18,0],
					[20,2],
					[20,7],
					[19,7],
					[19,2] ]);
				polygon(points=[
					[21,4],
					[23,6],
					[23,7],
					[21,5],
					 ]);
			}
		}
	}

	module	max1k1k() {
		linear_extrude(height=5) {
			union() {
				// 1
				polygon(points=[
					[0,0],
					[1,0],
					[7,6],
					[7,7],
					[6,7],
					[5,6],
					[6,6] ]);
				// 0
				translate([0,0,0]) { polygon(points=[
					[3,1],
					[3,0],
					[9,6],
					[12,6],
					[11,5],
					[6,3],
					[5,2],
					[10,4],
					[7,1],
					[5,1],
					[4,0],
					[7,0],
					[13,6],
					[13,7],
					[9,7],
					]); }
				// 0
				translate([6,0,0]) { polygon(points=[
					[3,1], [3,0], [9,6], [12,6], [11,5],
					[6,3], [5,2], [10,4], [7,1], [5,1],
					[4,0], [7,0], [13,6], [13,7], [9,7]
					]); }
				// 0
				translate([12,0,0]) { polygon(points=[
					[3,1], [3,0], [9,6], [12,6], [11,5],
					[6,3], [5,2], [10,4], [7,1], [5,1],
					[4,0], [7,0], [13,6], [13,7], [9,7]
					]); }
			}
		}
	}

	translate([0,0,0]) {
		max1k();

		translate([23,0,0]) {
			max1k1k();
		}
	}
}

max1klogo_w = 47;
max1klogo_l = 7;
max1klogo_h = 5;

module	max1kshell() {
	difference() {
		w = 2;
		translate([-w/2,-w/2,-w+0.2]) {
			cube([max1klogo_w+w, max1klogo_l+w, max1klogo_h]);
		}
		cube([max1klogo_w, max1klogo_l, max1klogo_h]);
	}
}

// max1kshell();
// max1klogo();

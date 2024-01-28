pragma circom 2.0.0;

template Crop(hOrig, wOrig, hNew, wNew, hStartNew, wStartNew) {
    signal input a;
    signal input b;

    signal input orig[hOrig][wOrig][3];

    signal input new[hNew][wNew][3];

    signal output c;


    for (var i = 0; i <  hNew; i++) {

		for (var j = 0; j < wNew; j++) {

			for (var k = 0; k < 3; k++) {
				new[i][j][k] === orig[hStartNew + i][wStartNew + j][k];	
			}		
		}		
	}
     c <== a*b;
 }

 component main = Crop(6632, 4976, 2048, 1363, 0, 0);
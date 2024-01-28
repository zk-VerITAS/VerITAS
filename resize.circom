pragma circom 2.0.0;


template Resize(hOrig, wOrig, hNew, wNew) {
    signal input a;
    signal input b;

    signal input orig[hOrig][wOrig][3];
    signal input new[hNew][wNew][3];
    signal input positiveRemainder[hNew][wNew][3];
    signal input negativeRemainder[hNew][wNew][3];

    signal output c;


    for (var i = 0; i < hNew; i++) {

		for (var j = 0; j < wNew; j++) {		

			var x_l = (wOrig - 1) * j \ (wNew - 1);

			var y_l = (hOrig - 1) * i \ (hNew - 1);

			var x_h = x_l * (wNew - 1) == (wOrig - 1) * j ? x_l : x_l + 1;

			var y_h = y_l * (hNew - 1) == (hOrig - 1) * i ? y_l : y_l + 1;

			

			var xRatioWeighted = ((wOrig - 1) * j) - (wNew - 1)*x_l;

			var yRatioWeighted = ((hOrig - 1) * i) - (hNew - 1)*y_l;



			var denom = (wNew - 1) * (hNew - 1);

			

			for (var k = 0; k < 3; k++) {
                            var sum = orig[y_l][x_l][k] * (wNew - 1 - xRatioWeighted) * (hNew - 1 - yRatioWeighted)
                            + orig[y_l][x_h][k] * xRatioWeighted * (hNew - 1 - yRatioWeighted)
                            + orig[y_h][x_l][k] * yRatioWeighted * (wNew - 1 - xRatioWeighted)
                            + orig[y_h][x_h][k] * xRatioWeighted * yRatioWeighted;
                            
                            new[i][j][k] * denom - positiveRemainder[i][j][k] + negativeRemainder[i][j][k] === sum;
              
                        } 					

		}		

	}

	c <== a*b;

}



component main = Resize(6632, 4976, 2048, 1363);


/*
pragma circom 2.0.0;


template Resize(hOrig, wOrig, hNew, wNew) {
    signal input a;
    signal input b;

    signal input orig[hOrig][wOrig][3];
    signal input new[hNew][wNew][3];

    signal output c;


    for (var i = 0; i < hNew; i++) {

		for (var j = 0; j < wNew; j++) {		

			var x_l = (wOrig - 1) * j \ (wNew - 1);

			var y_l = (hOrig - 1) * i \ (hNew - 1);

			var x_h = x_l * (wNew - 1) == (wOrig - 1) * j ? x_l : x_l + 1;

			var y_h = y_l * (hNew - 1) == (hOrig - 1) * i ? y_l : y_l + 1;

			

			var xRatioWeighted = ((wOrig - 1) * j) - (wNew - 1)*x_l;

			var yRatioWeighted = ((hOrig - 1) * i) - (hNew - 1)*y_l;



			var denom = (wNew - 1) * (hNew - 1);

			
                        for (var k = 0; k < 3; k++) {
                            var sum = orig[y_l][x_l][k] * (wNew - 1 - xRatioWeighted) * (hNew - 1 - yRatioWeighted)
                            + orig[y_l][x_h][k] * xRatioWeighted * (hNew - 1 - yRatioWeighted)
                            + orig[y_h][x_l][k] * yRatioWeighted * (wNew - 1 - xRatioWeighted)
                            + orig[y_h][x_h][k] * xRatioWeighted * yRatioWeighted;
                            
                            new[i][j][k] * denom === sum;
              
                        } 
								
		}		

	}

	c <== a*b;

}



component main = Resize(100, 100, 80, 20);*/
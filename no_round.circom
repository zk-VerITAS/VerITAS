pragma circom 2.0.0;

template GrayscaleChecker(h, w) {
    signal input a;
    signal input b;

    signal input orig[h][w][3];
    signal input gray[h][w];
    signal input negativeRemainder[h][w];    
    signal input positiveRemainder[h][w];

    signal output c;
 
    for (var i = 0; i < h; i++) {
        for (var j = 0; j < w; j++) {
            30 * orig[i][j][0] + 59 * orig[i][j][1] + 11 * orig[i][j][2] === 100 * gray[i][j] - negativeRemainder[i][j] + positiveRemainder[i][j]; 
        }       
        
    }

    
     c <== a*b;
}

component main = GrayscaleChecker(2048, 1364);
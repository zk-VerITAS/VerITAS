import math
import numpy as np
import json
import sys

def bilinear_circom(image, hOrig, wOrig, hNew, wNew):

  resized = np.empty([hNew, wNew, 3])
  positiveRemainder = np.empty([hNew, wNew, 3])
  negativeRemainder = np.empty([hNew, wNew, 3])

  for i in range(hNew):
    for j in range(wNew):
      for k in range(3):
           x_l2 = (int)((wOrig - 1) * j / (wNew - 1))
           y_l2 = (int)((hOrig - 1) * i / (hNew - 1))
           x_h2 = x_l2 if x_l2 * (wNew - 1) == (wOrig - 1) * j else x_l2 + 1
           y_h2 = y_l2 if y_l2 * (hNew - 1) == (hOrig - 1) * i else y_l2 + 1

           xRatioWeighted = ((wOrig - 1) * j) - (wNew - 1)*x_l2
           yRatioWeighted = ((hOrig - 1) * i) - (hNew - 1)*y_l2

           a = image[y_l2, x_l2, k]
           b = image[y_l2, x_h2, k]
           c = image[y_h2, x_l2, k]
           d = image[y_h2, x_h2, k]

           s = a * (wNew - 1 - xRatioWeighted) * (hNew - 1 - yRatioWeighted) \
                  + b * xRatioWeighted * (hNew - 1 - yRatioWeighted) \
                  + c * yRatioWeighted * (wNew - 1 - xRatioWeighted) \
                  + d * xRatioWeighted * yRatioWeighted

           new = (round)( s / ((wNew - 1) * (hNew - 1)))

           r = (round(new * (wNew - 1) * (hNew - 1) - s))
           
           resized[i][j][k] = new
           if r > 0:
                positiveRemainder[i][j][k] = r
                negativeRemainder[i][j][k] = 0
           else:
                negativeRemainder[i][j][k] = abs(r)
                positiveRemainder[i][j][k] = 0
               
      
  #print(positiveRemainder)
  #print(negativeRemainder)
  d = {}
  d['a'] = 4
  d['b'] = 7
  d['orig'] = image.tolist()
  d['new'] = resized.astype(int).tolist()
  d['negativeRemainder'] = negativeRemainder.astype(int).tolist()
  d['positiveRemainder'] = positiveRemainder.astype(int).tolist()
  
  with open('resize_input.json', 'w', encoding='utf-8') as f:
       json.dump(d, f, ensure_ascii=False, indent=4)
  return resized


def bilinear_resize(image, hNew, wNew):

  hOrig, wOrig = image.shape[:2]

  resized = np.empty([hNew, wNew])

  x_ratio = float(wOrig - 1) / (wNew - 1) if wNew > 1 else 0
  y_ratio = float(hOrig - 1) / (hNew - 1) if hNew > 1 else 0

  for i in range(hNew):
    for j in range(wNew):

      x_l, y_l = math.floor(x_ratio * j), math.floor(y_ratio * i)
      x_h, y_h = math.ceil(x_ratio * j), math.ceil(y_ratio * i)

      x_l2 = (int)((wOrig - 1) * j / (wNew - 1))
      y_l2 = (int)((hOrig - 1) * i / (hNew - 1))
      x_h2 = x_l2 if x_l2 * (wNew - 1) == (wOrig - 1) * j else x_l2 + 1
      y_h2 = y_l2 if y_l2 * (hNew - 1) == (hOrig - 1) * i else y_l2 + 1

      assert(x_l == x_l2)
      assert(y_l == y_l2)
      assert(x_h == x_h2)
      assert(y_h == y_h2)

      x_weight = (x_ratio * j) - x_l
      y_weight = (y_ratio * i) - y_l

      xRatioWeighted = ((wOrig - 1) * j) - (wNew - 1)*x_l2
      yRatioWeighted = ((hOrig - 1) * i) - (hNew - 1)*y_l2
      assert(round((1 - x_weight) * (wNew - 1)) == (wNew - 1 - xRatioWeighted))
      assert(round(x_weight * (wNew - 1)) == xRatioWeighted)
      assert(round((1 - y_weight) * (hNew - 1)) == (hNew - 1 - yRatioWeighted))
      assert(round(y_weight * (hNew - 1)) == yRatioWeighted)

      a = image[y_l, x_l]
      b = image[y_l, x_h]
      c = image[y_h, x_l]
      d = image[y_h, x_h]

      pixel = (int) (a * (1 - x_weight) * (1 - y_weight) \
              + b * x_weight * (1 - y_weight) \
              + c * y_weight * (1 - x_weight) \
              + d * x_weight * y_weight)

      resized[i][j] = pixel

      test = (int) ((a * (wNew - 1 - xRatioWeighted) * (hNew - 1 - yRatioWeighted) \
             + b * xRatioWeighted * (hNew - 1 - yRatioWeighted) \
             + c * yRatioWeighted * (wNew - 1 - xRatioWeighted) \
             + d * xRatioWeighted * yRatioWeighted) / ((wNew - 1) * (hNew - 1)))


      assert(abs(test - pixel) <= 1)
      

  return resized



x = np.array([[114., 195., 254., 217.,  33., 160.],
       [110.,  91., 184., 143., 190., 124.],
       [212., 163., 245.,  39.,  83., 188.]])

'''x = np.array([[114., 195., 254., 217.,  33., 160., 114., 195., 254., 217.,  33., 160., 114., 195., 254., 217.,  33., 160.],
              [110.,  91., 184., 143., 190., 124., 110.,  91., 184., 143., 190., 124., 110.,  91., 184., 143., 190., 124.],
              [0., 0., 0.,  0.,  0., 0., 0., 0., 0.,  0.,  0., 0., 0., 0., 0.,  0.,  0., 0.],
              [114., 195., 254., 217.,  33., 160., 114., 195., 254., 217.,  33., 160., 114., 195., 254., 217.,  33., 160.],
              [110.,  91., 184., 143., 190., 124., 110.,  91., 184., 143., 190., 124., 110.,  91., 184., 143., 190., 124.],
              [0., 0., 0.,  0.,  0., 0., 0., 0., 0.,  0.,  0., 0., 0., 0., 0.,  0.,  0., 0.],
              [114., 195., 254., 217.,  33., 160., 114., 195., 254., 217.,  33., 160., 114., 195., 254., 217.,  33., 160.],
              [110.,  91., 184., 143., 190., 124., 110.,  91., 184., 143., 190., 124., 110.,  91., 184., 143., 190., 124.],
              [0., 0., 0.,  0.,  0., 0., 0., 0., 0.,  0.,  0., 0., 0., 0., 0.,  0.,  0., 0.]])

x = np.array([[114., 195., 254., 217.,  33., 160.],
       [110.,  91., 184., 143., 190., 124.],
       [212., 163., 245.,  39.,  83., 188.],
       [ 23., 206.,  62.,   7.,   5., 206.],
       [152., 177., 118., 155., 245.,  41.]])

x = np.array([[114., 195., 254., 217.],
       [110.,  91., 184., 143.],
       [212., 163., 245.,  39.]])'''

x = np.array([[114, 195, 254, 217,  33, 160],
       [110,  91, 184, 143, 190, 124],
       [212, 163, 245,  39,  83, 188],
       [ 23, 206,  62,   7,   5, 206],
       [152, 177, 118, 155, 245,  41]])

#x = np.array([[1, 2, 3, 4, 5],[6, 7, 8, 9, 10],[11, 12, 13, 14, 15],[16, 17, 18, 19, 20]])
#x = np.empty([4, 4])
#print(bilinear_resize(x, 3, 2))
hOrig = int(sys.argv[1])
wOrig = int(sys.argv[2])
hNew = int(sys.argv[3])
wNew = int(sys.argv[4])
x = np.random.randint(256, size=(hOrig, wOrig, 3))
#print(x)
bilinear_circom(x, hOrig, wOrig, hNew, wNew)
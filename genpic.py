import random
import sys

prefix = sys.argv[1]
imageSize = int(sys.argv[2])
pixelLength = int(sys.argv[3])

pixels = []
f = open(prefix + "_image_" + str(imageSize) + "_" + str(pixelLength) + ".txt", "w")
for i in range(imageSize):
	#f.write(str(i))
	pixel = str(random.randint(0, 2**pixelLength - 1))
	pixels.append(pixel)
	f.write(pixel)
	f.write("\n")


r = 52435875175126190479447740508185965837690552500527637822603658699938581184513

f = open(prefix + "_hash_" + str(imageSize) + "_" + str(pixelLength) + ".txt", "w")
for i in range(imageSize):
	#f.write(str(i))
	f.write(str(random.randint(0, r - 1)))
	f.write("\n")
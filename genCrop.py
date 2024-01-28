import numpy as np
import json
import sys

hOrig = int(sys.argv[1])
wOrig = int(sys.argv[2])
hNew = int(sys.argv[3])
wNew = int(sys.argv[4])
hStartNew = int(sys.argv[5])
wStartNew = int(sys.argv[6])
x = np.random.randint(256, size=(hOrig, wOrig, 3))

d = {}
d['a'] = '2'
d['b'] = '7'
d['orig'] = x.tolist()
d['new'] = (x[hStartNew : hStartNew + hNew, wStartNew : wStartNew + wNew]).tolist()
# print(d)
with open('crop_input.json', 'w', encoding='utf-8') as f:
     json.dump(d, f, ensure_ascii=False, indent=4)

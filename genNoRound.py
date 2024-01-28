import sys
import json
import numpy as np

h = int(sys.argv[1])
w = int(sys.argv[2])

d = {}
d['a'] = 2
d['b'] = 4
d['orig'] = []
d['gray'] = []
d['negativeRemainder'] = []
d['positiveRemainder'] = []

orig_row = []
gray_row = []
neg_row = []
pos_row = []

for i in range(int(w/2)):
     orig_row.append([150, 93, 200])
     orig_row.append([45, 239, 97])
     gray_row.append(122)
     gray_row.append(165)
     neg_row.append(13)
     neg_row.append(0)
     pos_row.append(0)
     pos_row.append(18)


for i in range(h):
     d['orig'].append(orig_row)
     d['gray'].append(gray_row)
     d['negativeRemainder'].append(neg_row)
     d['positiveRemainder'].append(pos_row)

     
with open('no_round_input.json', 'w', encoding='utf-8') as f:
     json.dump(d, f, ensure_ascii=False, indent=4)

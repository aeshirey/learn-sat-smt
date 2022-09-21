#!/usr/bin/python3
from z3 import *
from PIL import Image, ImageDraw # for rendering the output
from time import time
import random
random.seed(0) # for reproducibility

CONTAINER_SIZE = (420, 420)
CONTAINER_AREA = CONTAINER_SIZE[0] * CONTAINER_SIZE[1]
NUM_BOXES = 30
MIN_BOX_SIZE = (40, 40)
MAX_BOX_SIZE = (100, 100)

boxes = [ (random.randint(MIN_BOX_SIZE[0], MAX_BOX_SIZE[0]+1), random.randint(MIN_BOX_SIZE[1], MAX_BOX_SIZE[1]+1))
        for _ in range(NUM_BOXES)]

# If the sum of area of all boxes exceeds the container size, then we certainly can't fit them all in
boxes_area = sum(w*h for (w,h) in boxes)
print(f'Boxes occupy {boxes_area} space in a container of size {CONTAINER_AREA} ({boxes_area/CONTAINER_AREA})')
assert CONTAINER_AREA >= boxes_area

s = Solver()

# We'll store the X and Y dimensions of every box. "(X 1)" returns the X position of box 1
X = Function('X', IntSort(), IntSort())
Y = Function('Y', IntSort(), IntSort())

# Every box must be within the bounds of the container
for (b, (w,h)) in enumerate(boxes):
    s.add(
        X(b+1) >= 0,
        X(b+1) < CONTAINER_SIZE[0] - w,
        Y(b+1) >= 0,
        Y(b+1) < CONTAINER_SIZE[1] - h,
        )

# No box may overlap any other box. This can be thought of as:
#    OR (box0 must be to the left of box1)
#       (box0 must be to the right of box1)
#       (box0 must be above box1)
#       (box0 must be below box1)

for (b0, (w0, h0)) in enumerate(boxes[:-1]):
    for b1 in range(b0+1, len(boxes)):
        w1, h1 = boxes[b1]
        s.add(Or(
            X(b0+1) + w0 < X(b1+1), # b0 is left of b1
            X(b1+1) + w1 < X(b0+1), # b1 is left of b0
            Y(b0+1) + h0 < Y(b1+1), # b0 is above b1
            Y(b1+1) + h1 < Y(b0+1), # b1 is above b0
            ))

with open('packed-rectangles.smt2', 'w') as fh:
    fh.write(s.sexpr())

start = time()
if unsat == s.check():
    print(f'Verification failed after {time()-start} sec')
    exit()

print(f'Verification took {time()-start} sec')
m = s.model()

img = Image.new('RGB', CONTAINER_SIZE)
draw = ImageDraw.Draw(img)

draw.rectangle(((0,0), CONTAINER_SIZE), fill=(120, 120, 120), outline='black') # set a gray background to the image

for (b, (w,h)) in enumerate(boxes):
    x = m.eval(X(b+1)).as_long()
    y = m.eval(Y(b+1)).as_long()
    shape = ((x,y), (x+w, y+h))
    draw.rectangle(shape, fill=(124, 76, 43), outline='black')
    print(f'Box{b+1} @ ({x},{y}); width={w}, height={h}')

img.save('packed-rectangles.png')
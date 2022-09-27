#!/usr/bin/python3
from z3 import *
from PIL import Image, ImageDraw # for rendering the output
from time import time
import random
random.seed(0) # for reproducibility

CONTAINER_WIDTH = 400
NUM_BOXES = 15
MIN_BOX_SIZE = (40, 40)
MAX_BOX_SIZE = (100, 100)

boxes = [ (random.randint(MIN_BOX_SIZE[0], MAX_BOX_SIZE[0]+1), random.randint(MIN_BOX_SIZE[1], MAX_BOX_SIZE[1]+1))
        for _ in range(NUM_BOXES)]

o = Optimize()

# We'll minimimze this value
container_height = Int('container_height')

# And we know that it must be at least this tall to ride
o.add(container_height > sum(w*h for (w,h) in boxes) / CONTAINER_WIDTH)

# Store the X and Y dimensions of every box. "(X 1)" returns the X position of box 1
X = Function('X', IntSort(), IntSort())
Y = Function('Y', IntSort(), IntSort())


# Every box must be within the bounds of the container
for (b, (w,h)) in enumerate(boxes):
    o.add(
        X(b+1) >= 0,
        X(b+1) < CONTAINER_WIDTH - w,
        Y(b+1) >= 0,
        Y(b+1) < container_height - h,
        )

# No box may overlap any other box. This can be thought of as:
#    OR (box0 must be to the left of box1)
#       (box0 must be to the right of box1)
#       (box0 must be above box1)
#       (box0 must be below box1)

for (b0, (w0, h0)) in enumerate(boxes[:-1]):
    for b1 in range(b0+1, len(boxes)):
        w1, h1 = boxes[b1]
        o.add(Or(
            X(b0+1) + w0 < X(b1+1), # b0 is left of b1
            X(b1+1) + w1 < X(b0+1), # b1 is left of b0
            Y(b0+1) + h0 < Y(b1+1), # b0 is above b1
            Y(b1+1) + h1 < Y(b0+1), # b1 is above b0
            ))

with open('packed-rectangles-minimized.smt2', 'w') as fh:
    fh.write(o.sexpr())

minimized_height = o.minimize(container_height)

start = time()
if sat != o.check():
    print(f'Verification failed after {time()-start} sec')
    exit()


print(f'Verification took {time()-start} sec')
m = o.model()
minimized_height_val = minimized_height.value().as_long()


container_size = (CONTAINER_WIDTH, minimized_height_val)
img = Image.new('RGB', container_size)
draw = ImageDraw.Draw(img)

draw.rectangle(((0,0), container_size), fill=(120, 120, 120), outline='black') # set a gray background to the image

for (b, (w,h)) in enumerate(boxes):
    x = m.eval(X(b+1)).as_long()
    y = m.eval(Y(b+1)).as_long()
    shape = ((x,y), (x+w, y+h))
    draw.rectangle(shape, fill=(124, 76, 43), outline='black')
    print(f'Box{b+1} @ ({x},{y}); width={w}, height={h}')

img.save('packed-rectangles-minimized.png')
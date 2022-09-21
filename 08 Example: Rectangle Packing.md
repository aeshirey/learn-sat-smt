# Rectangle-Packing

The [Rectangle packing problem](https://en.wikipedia.org/wiki/Rectangle_packing) is a problem where "the objective is to determine whether a given set of small rectangles can be placed inside a given large polygon, such that no two small rectangles overlap."

_Note: Due to the ever-increasing number of s-expressions required for problems such as this, the primary focus will be on the Z3 Python API. A few raw s-expressions will be shown for demonstration, but the implementation will be in Python._

For ease of use, we'll start with a few configuration values:

```python
CONTAINER_SIZE = (420, 420)
CONTAINER_AREA = CONTAINER_SIZE[0] * CONTAINER_SIZE[1]
NUM_BOXES = 30
MIN_BOX_SIZE = (40, 40)
MAX_BOX_SIZE = (100, 100)
```

These values are somewhat arbitrarily chosen, though as you'll see below, the parameters of our search are incredibly important to its success.

For demonstration, we'll generate some boxes of random sizes and ensure that these boxes will, in fact, fit in the overall container:

```python
boxes = [ (random.randint(MIN_BOX_SIZE[0], MAX_BOX_SIZE[0]+1),
           random.randint(MIN_BOX_SIZE[1], MAX_BOX_SIZE[1]+1))
        for _ in range(NUM_BOXES)]

boxes_area = sum(w*h for (w,h) in boxes)
assert CONTAINER_AREA >= boxes_area
```

Using a random seed of 0 and the above specifications, the boxes combine to occupy an area of 163,462. With a container area of 176,400, this means our boxes would occupy 92.7% of the total space.

## Setting up Constraints

Now we can start applying constraints to the solution. Using  two functions to track the (x,y) coordinates of every box, we can assert that every box must fit inside the container. Note that I'm using 1-indexing in the (eg, `(X 1)` is the x-coordinate of the first box, not `(X 0)`).

```python
X = Function('X', IntSort(), IntSort())
Y = Function('Y', IntSort(), IntSort())

for (b, (w,h)) in enumerate(boxes):
    s.add(
        X(b+1) >= 0,
        X(b+1) < CONTAINER_SIZE[0] - w,
        Y(b+1) >= 0,
        Y(b+1) < CONTAINER_SIZE[1] - h,
        )
```

The next requirement is that boxes may not overlap each other. We can ensure this by requiring that for any two boxes `box0` and `box1`,

* box0 is to the left of box1, or
* box0 is to the right of box1, or
* box0 is above box1, or
* box0 is below box1

 This is concisely represented in the Python code but generates a large number of s-expressions internally (over 1800 lines of SMT when output from our `Solver` with `s.sexpr()`):

```python
for (b0, (w0, h0)) in enumerate(boxes[:-1]):
    for b1 in range(b0+1, len(boxes)):
        w1, h1 = boxes[b1]
        s.add(Or(
            X(b0+1) + w0 < X(b1+1), # b0 is left of b1
            X(b1+1) + w1 < X(b0+1), # b1 is left of b0
            Y(b0+1) + h0 < Y(b1+1), # b0 is above b1
            Y(b1+1) + h1 < Y(b0+1), # b1 is above b0
            ))
```

Perhaps surprisingly, this is all we need. Checking satisfiability on this input, however, is exceptionally intense: on my desktop running [WSL2](https://devblogs.microsoft.com/commandline/announcing-wsl-2/), Z3 returns `sat` after 9hr24min.

## Interacting with the model
With the model, `m`, generated from `s.model()`, you can easily interact with it by calling the `m.eval()` function, passing in the Z3 constant. For example, to get the (x,y) coordinates of box7:

```python
x = m.eval(X(7))
y = m.eval(Y(7))
```

Both `x` and `y` are of type `z3.z3.IntNumRef` from which you can get values using the `.as_long()` or `.as_string()` methods, getting proper Python types.

## Visualizing the Results
With the model produced, we'll use [Pillow](https://python-pillow.org/) to visualize the results.

```python
from PIL import Image, ImageDraw

img = Image.new('RGB', CONTAINER_SIZE)
draw = ImageDraw.Draw(img)

# set a gray background to the image
draw.rectangle(((0,0), CONTAINER_SIZE), 
               fill=(120, 120, 120),
               outline='black')

for (b, (w,h)) in enumerate(boxes):
    x = m.eval(X(b+1)).as_long()
    y = m.eval(Y(b+1)).as_long()
    shape = ((x,y), (x+w, y+h))
    draw.rectangle(shape, fill=(124, 76, 43), outline='black')

img.save('packed-rectangles.png')
```

![Packed rectangles visualized](/resources/packed-rectangles.png)

The full Python code is available [here](/08%20rectangle-packing.py).

---

Next, let's explore a derivation of prime checks by [generating a prime value using `forall`](/09%20Forall.md).
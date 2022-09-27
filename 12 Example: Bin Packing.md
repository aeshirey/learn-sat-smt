# Optimal Bin Packing
[Bin packing](https://en.wikipedia.org/wiki/Bin_packing_problem) is a variation on the [rectangle packing](/08%20Example%3A%20Rectangle%20Packing.md) we previously did, "in which items of different sizes must be packed into a finite number of bins or containers, each of a fixed given capacity, in a way that minimizes the number of bins used." The difference is that rectangle packing merely tries to fit items into a fixed-size container while bin packing reduces the size of the container to the minimum possible size.

This example integrates what we learned in [optimization](/10%20Optimization.md) into the rectangle packing. This time around, due to the computational complexity, we'll halve the number of boxes and slightly reduce the container width.

```python
CONTAINER_WIDTH = 400
NUM_BOXES = 15
MIN_BOX_SIZE = (40, 40)
MAX_BOX_SIZE = (100, 100)

boxes = [ (random.randint(MIN_BOX_SIZE[0], MAX_BOX_SIZE[0]+1),
          random.randint(MIN_BOX_SIZE[1], MAX_BOX_SIZE[1]+1))
        for _ in range(NUM_BOXES)]
```

You'll note that the `CONTAINER_HEIGHT` is not specified. This is because we're going to let Z3 optimize the container height for us:

```python
o = Optimize()
container_height = Int('container_height')
```

To help improve the constraints, we can determine what the minimum container height must be based on the total bin areas and the pre-defined container width:

```python
o.add(container_height > 
    sum(w*h for (w,h) in boxes) / CONTAINER_WIDTH)
```

And we'll also change the value used in constraining where any box is placed:

```python
X = Function('X', IntSort(), IntSort())
Y = Function('Y', IntSort(), IntSort())

for (b, (w,h)) in enumerate(boxes):
    o.add(
        X(b+1) >= 0,
        X(b+1) < CONTAINER_WIDTH - w,
        Y(b+1) >= 0,
        Y(b+1) < container_height - h, # This is different
        )
```

Finally, we can tell Z3 that we're optimizing (specifically, a minimization) the container's height:

```python
minimized_height = o.minimize(container_height)
```

With this, we can run [the full script](/12%20bin-packing.py). Whereas the previous problem took 9.5 hours, this minimization takes _44.5 hours_ to run on the same machine.

![Minimized, packed rectangles](/resources/packed-rectangles-minimized.png)
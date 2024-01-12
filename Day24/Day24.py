import sympy

# For part 1, see Day24.idr

with open("Day24/input") as f:
    input = [
        tuple(map(int, line.replace(",", "").replace("@", "").split()))
        for line in f.readlines()[:3]
    ]

t1, t2, t3, x, y, z, dx, dy, dz = sympy.symbols(["t1", "t2", "t3", "x", "y", "z", "dx", "dy", "dz"])

eqs = [
    eq
    for ((hx, hy, hz, dhx, dhy, dhz), t) in zip(input, [t1, t2, t3])
    for eq in [
        hx + t * dhx - x - t * dx,
        hy + t * dhy - y - t * dy,
        hz + t * dhz - z - t * dz,
    ]
]

[(t1, t2, t3, x, y, z, dx, dy, dz)] = sympy.solve(eqs, [t1, t2, t3, x, y, z, dx, dy, dz])

print("Part 2")
print(x + y + z)

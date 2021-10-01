import matplotlib.pyplot as plt
import numpy as np

plt.rcParams.update({
    "text.usetex": True,
    "font.family": "sans-serif",
    "font.sans-serif": ["Helvetica"]
})

num_points = 101

x, y = np.linspace(-5, 5, num_points), np.linspace(-5, 5, num_points)

def mink_dist(x1, x2):
    return -pow(x1[0] - x2[0], 2) + pow(x1[1] - x2[1], 2)

dists = np.zeros((num_points, num_points))
for i, xv in enumerate(x):
    for j, yv in enumerate(y):
        dists[i, j] = mink_dist((0,0), (xv, yv))

plt.pcolormesh(x, y, dists, shading="auto", cmap="magma")
plt.colorbar()
plt.contour(x, y, dists, colors="white", levels=10)
plt.title(r"Distance (squared) from origin using $\eta_{\mu\nu}$ in 2D")
plt.xlabel(r"$x$ (space)")
plt.ylabel(r"$t$ (time)")
plt.show()

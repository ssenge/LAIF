"""Best linear factor of iid normals of radius R on the d-regular tree, sign rounding (the class of the
explicit vector algorithm and of truncated normal waves). Valid at girth 2R + 2. Cut = arccos(rho)/pi.
f_v = sum_l a_l (sum of the seeds at distance l); with b_l = a_l sqrt(#vertices at distance l), rho is the smallest
eigenvalue of a tridiagonal matrix with off-diagonal 1/sqrt(d), then sqrt(d - 1)/d."""
import numpy as np


def best(d, R):
    off = np.full(R, np.sqrt(d - 1) / d); off[0] = 1 / np.sqrt(d)
    T = np.diag(off, 1) + np.diag(off, -1)
    return np.arccos(max(-1.0, np.linalg.eigvalsh(T)[0])) / np.pi


if __name__ == "__main__":
    assert abs(best(4, 2) - 0.7301) < 1e-4 and abs(best(3, 1) - np.arccos(-1 / np.sqrt(3)) / np.pi) < 1e-12
    for d in (4, 6, 8, 10, 20, 30, 40):
        print(d, [round(best(d, R), 4) for R in range(1, 15)])

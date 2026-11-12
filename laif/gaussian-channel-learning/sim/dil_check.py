# Theorem 3: the numerical constants of the proof.
import numpy as np
# constants
for m in range(1, 200):
    assert np.sqrt(6) + np.sqrt(10) + 5 * np.sqrt(4 * m) <= 16 * np.sqrt(m)
g = lambda x: np.sqrt(np.pi / (x + 1)) + np.sqrt(2 * x)
xs = np.linspace(1, 2, 10001)
assert g(xs).max() <= 3.3
assert 3.3 * np.sqrt(32) <= 18.7 and 18.7 * np.sqrt(416) <= 382 and 382 / np.sqrt(416) > 1
assert 2 * (1 + np.sqrt(3)) / 8 <= 0.7
print("Theorem 3 constants: sqrt6 + sqrt10 + 10 sqrt m <= 16 sqrt m, g <= 3.3 on [1, 2], 3.3 sqrt32 <= 18.7, 18.7 sqrt416 <= 382")


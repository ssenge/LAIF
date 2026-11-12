"""Price-based APDV in the configuration used for every table: logit over the current downhill successors, virtual
queues on offered inflow at rho 0.95, per-link price cap 5 x free-flow time, price period 1 min; learned: a day-to-day
price profile (30 days, step 1 min per day) plus a within-day price with gain 0.3 and origin holding 0.5; cold
start: no profile, gain 3, no holding."""
import numpy as np

import dnl
import logit

DAYS, RHO = 30, 0.95


def price(a_ff, G, sf, U, g, prof=None, hold=None, eps=None):
    return dnl.Price(a_ff, "exit", g, RHO, 1.0, U=U, soft=sf, dyn=True, prof=prof, hold=hold, lmax=5 * G.g.fft, eps=eps)


def learned(sim, a_ff, G, sf, U, eps=None):
    """Learn the profile on sim for DAYS days; return a factory for the learned policy."""
    prof = dnl.learn(sim, lambda P: price(a_ff, G, sf, U, 0.3, P, 0.5), DAYS, 1.0, RHO)[1]
    return lambda: price(a_ff, G, sf, U, 0.3, prof, 0.5, eps)


def cold(a_ff, G, sf, U):
    return lambda: price(a_ff, G, sf, U, 3.0)


def theta(name):
    return 1.0 if name == "SiouxFalls" else 3.0


def soft(G, Q, name):
    return logit.Soft(G, Q, theta(name), G.g.fft.copy())

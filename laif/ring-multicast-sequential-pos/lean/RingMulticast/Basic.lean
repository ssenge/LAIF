import Mathlib.Tactic.Linarith
import Mathlib.Data.Rat.Defs

/-!
# Linear bounds for the multicast game on a ring

Each theorem is one case of the bound z ≤ 1/3, where z = min(s − a_p, s − a_{q+1}), s is the cost of a most
expensive edge and the optimum is normalized to 1. The hypotheses are the relaxed best-response conditions of
that case, as linear inequalities in nonnegative rationals. Players p (order A) and q (order B) are the first
players to deviate from the optimum, and d = p − q.
-/

/-- Case q ≥ p. Variables: a_p, the mass left of p, a_{q+1}, s, z. -/
theorem bound_q_ge_p (ap P aq1 s z : ℚ)
    (n_ap : 0 ≤ ap)
    (n_P : 0 ≤ P)
    (n_aq1 : 0 ≤ aq1)
    (n_s : 0 ≤ s)
    (h_A_p : (-1:ℚ)*ap + ((-1:ℚ)/2)*P + (1:ℚ)*s ≤ (0:ℚ))
    (h_B_q : ((3:ℚ)/2)*ap + ((3:ℚ)/2)*P + ((-1:ℚ)/2)*aq1 + ((-1:ℚ)/2)*s ≤ ((1:ℚ)/2))
    (h_cap_p : (1:ℚ)*ap + (-1:ℚ)*s ≤ (0:ℚ))
    (h_cap_q1 : (1:ℚ)*aq1 + (-1:ℚ)*s ≤ (0:ℚ))
    (h_mass : (1:ℚ)*ap + (1:ℚ)*P ≤ (1:ℚ))
    (h_zA : (1:ℚ)*ap + (-1:ℚ)*s + (1:ℚ)*z ≤ (0:ℚ))
    (h_zB : (1:ℚ)*aq1 + (-1:ℚ)*s + (1:ℚ)*z ≤ (0:ℚ)) :
    z ≤ ((1:ℚ)/5) := by
  linarith

/-- Case q + 1 = p ≥ 1. Variables: a_p, the mass left of p, s, z. -/
theorem bound_q_succ_eq_p (ap L s z : ℚ)
    (n_ap : 0 ≤ ap)
    (n_L : 0 ≤ L)
    (n_s : 0 ≤ s)
    (h_A_p : (-1:ℚ)*ap + ((-1:ℚ)/2)*L + (1:ℚ)*s ≤ (0:ℚ))
    (h_B_q : ((-1:ℚ)/2)*ap + ((3:ℚ)/2)*L + ((-1:ℚ)/2)*s ≤ ((1:ℚ)/2))
    (h_cap_p : (1:ℚ)*ap + (-1:ℚ)*s ≤ (0:ℚ))
    (h_mass : (1:ℚ)*ap + (1:ℚ)*L ≤ (1:ℚ))
    (h_zA : (1:ℚ)*ap + (-1:ℚ)*s + (1:ℚ)*z ≤ (0:ℚ)) :
    z ≤ ((1:ℚ)/3) := by
  linarith

/-- Case d = 2, q ≥ 0. Variables: U (mass up to q), a_{q+1}, a_{q+2}, s, z. -/
theorem bound_d2 (U b1 b2 s z : ℚ)
    (n_U : 0 ≤ U)
    (n_b1 : 0 ≤ b1)
    (n_b2 : 0 ≤ b2)
    (n_s : 0 ≤ s)
    (h_A_p : ((-1:ℚ)/3)*U + ((-1:ℚ)/2)*b1 + (-1:ℚ)*b2 + (1:ℚ)*s ≤ (0:ℚ))
    (h_AL : (1:ℚ)*U + (2:ℚ)*b1 + (-1:ℚ)*s ≤ (1:ℚ))
    (h_B_q : ((4:ℚ)/3)*U + ((-2:ℚ)/3)*b1 + ((-1:ℚ)/6)*b2 + ((-1:ℚ)/3)*s ≤ ((1:ℚ)/3))
    (h_BR1 : (-1:ℚ)*U + (-1:ℚ)*b1 + (1:ℚ)*b2 ≤ (0:ℚ))
    (h_cap1 : (1:ℚ)*b1 + (-1:ℚ)*s ≤ (0:ℚ))
    (h_cap2 : (1:ℚ)*b2 + (-1:ℚ)*s ≤ (0:ℚ))
    (h_Q__0 : (1:ℚ)*U + (1:ℚ)*b1 + (1:ℚ)*b2 ≤ (1:ℚ))
    (h_zA : (1:ℚ)*b2 + (-1:ℚ)*s + (1:ℚ)*z ≤ (0:ℚ))
    (h_zB : (1:ℚ)*b1 + (-1:ℚ)*s + (1:ℚ)*z ≤ (0:ℚ)) :
    z ≤ ((5:ℚ)/17) := by
  linarith

/-- Case d = 2, q = −1 (no left-goer in order B). -/
theorem bound_d2_none (U b1 b2 s z : ℚ)
    (n_U : 0 ≤ U)
    (n_b1 : 0 ≤ b1)
    (n_b2 : 0 ≤ b2)
    (n_s : 0 ≤ s)
    (h_A_p : ((-1:ℚ)/3)*U + ((-1:ℚ)/2)*b1 + (-1:ℚ)*b2 + (1:ℚ)*s ≤ (0:ℚ))
    (h_AL : (1:ℚ)*U + (2:ℚ)*b1 + (-1:ℚ)*s ≤ (1:ℚ))
    (h_BR1 : (-1:ℚ)*U + (-1:ℚ)*b1 + (1:ℚ)*b2 ≤ (0:ℚ))
    (h_cap1 : (1:ℚ)*b1 + (-1:ℚ)*s ≤ (0:ℚ))
    (h_cap2 : (1:ℚ)*b2 + (-1:ℚ)*s ≤ (0:ℚ))
    (h_Q__0 : (1:ℚ)*U + (1:ℚ)*b1 + (1:ℚ)*b2 ≤ (1:ℚ))
    (h_zA : (1:ℚ)*b2 + (-1:ℚ)*s + (1:ℚ)*z ≤ (0:ℚ))
    (h_zB : (1:ℚ)*b1 + (-1:ℚ)*s + (1:ℚ)*z ≤ (0:ℚ)) :
    z ≤ ((1:ℚ)/3) := by
  linarith

/-- Case d = 3, q ≥ 0. Variables: U (mass left of q), a_q, a_{q+1}, a_{q+2}, a_{q+3}, s, z. -/
theorem bound_d3 (U c0 b1 b2 b3 s z : ℚ)
    (n_U : 0 ≤ U)
    (n_c0 : 0 ≤ c0)
    (n_b1 : 0 ≤ b1)
    (n_b2 : 0 ≤ b2)
    (n_b3 : 0 ≤ b3)
    (n_s : 0 ≤ s)
    (h_A_p : ((-1:ℚ)/5)*U + ((-1:ℚ)/4)*c0 + ((-1:ℚ)/3)*b1 + ((-1:ℚ)/2)*b2 + (-1:ℚ)*b3 + (1:ℚ)*s ≤ (0:ℚ))
    (h_AL : (1:ℚ)*U + ((4:ℚ)/3)*c0 + ((3:ℚ)/2)*b1 + (2:ℚ)*b2 + (-1:ℚ)*s ≤ (1:ℚ))
    (h_B_q : ((5:ℚ)/4)*U + ((5:ℚ)/4)*c0 + ((-3:ℚ)/4)*b1 + ((-1:ℚ)/4)*b2 + ((-1:ℚ)/12)*b3 + ((-1:ℚ)/4)*s ≤ ((1:ℚ)/4))
    (h_BR1 : (-1:ℚ)*U + (-1:ℚ)*c0 + (-1:ℚ)*b1 + (1:ℚ)*b2 + ((1:ℚ)/2)*b3 ≤ (0:ℚ))
    (h_BR2 : (-1:ℚ)*U + (-1:ℚ)*c0 + (-1:ℚ)*b1 + (-1:ℚ)*b2 + (1:ℚ)*b3 ≤ (0:ℚ))
    (h_cap1 : (1:ℚ)*c0 + (-1:ℚ)*s ≤ (0:ℚ))
    (h_cap2 : (1:ℚ)*b1 + (-1:ℚ)*s ≤ (0:ℚ))
    (h_cap3 : (1:ℚ)*b2 + (-1:ℚ)*s ≤ (0:ℚ))
    (h_cap4 : (1:ℚ)*b3 + (-1:ℚ)*s ≤ (0:ℚ))
    (h_Q__0 : (1:ℚ)*U + (1:ℚ)*c0 + (1:ℚ)*b1 + (1:ℚ)*b2 + (1:ℚ)*b3 ≤ (1:ℚ))
    (h_zA : (1:ℚ)*b3 + (-1:ℚ)*s + (1:ℚ)*z ≤ (0:ℚ))
    (h_zB : (1:ℚ)*b1 + (-1:ℚ)*s + (1:ℚ)*z ≤ (0:ℚ)) :
    z ≤ ((110:ℚ)/333) := by
  linarith

/-- Case d = 3, q = −1. -/
theorem bound_d3_none (U c0 b1 b2 b3 s z : ℚ)
    (n_U : 0 ≤ U)
    (n_c0 : 0 ≤ c0)
    (n_b1 : 0 ≤ b1)
    (n_b2 : 0 ≤ b2)
    (n_b3 : 0 ≤ b3)
    (n_s : 0 ≤ s)
    (h_A_p : ((-1:ℚ)/5)*U + ((-1:ℚ)/4)*c0 + ((-1:ℚ)/3)*b1 + ((-1:ℚ)/2)*b2 + (-1:ℚ)*b3 + (1:ℚ)*s ≤ (0:ℚ))
    (h_AL : (1:ℚ)*U + ((4:ℚ)/3)*c0 + ((3:ℚ)/2)*b1 + (2:ℚ)*b2 + (-1:ℚ)*s ≤ (1:ℚ))
    (h_BR1 : (-1:ℚ)*U + (-1:ℚ)*c0 + (-1:ℚ)*b1 + (1:ℚ)*b2 + ((1:ℚ)/2)*b3 ≤ (0:ℚ))
    (h_BR2 : (-1:ℚ)*U + (-1:ℚ)*c0 + (-1:ℚ)*b1 + (-1:ℚ)*b2 + (1:ℚ)*b3 ≤ (0:ℚ))
    (h_cap1 : (1:ℚ)*c0 + (-1:ℚ)*s ≤ (0:ℚ))
    (h_cap2 : (1:ℚ)*b1 + (-1:ℚ)*s ≤ (0:ℚ))
    (h_cap3 : (1:ℚ)*b2 + (-1:ℚ)*s ≤ (0:ℚ))
    (h_cap4 : (1:ℚ)*b3 + (-1:ℚ)*s ≤ (0:ℚ))
    (h_Q__0 : (1:ℚ)*U + (1:ℚ)*c0 + (1:ℚ)*b1 + (1:ℚ)*b2 + (1:ℚ)*b3 ≤ (1:ℚ))
    (h_zA : (1:ℚ)*b3 + (-1:ℚ)*s + (1:ℚ)*z ≤ (0:ℚ))
    (h_zB : (1:ℚ)*b1 + (-1:ℚ)*s + (1:ℚ)*z ≤ (0:ℚ)) :
    z ≤ ((110:ℚ)/333) := by
  linarith

/-- Case d ≥ 4. Variables: a_p, a_{p−1}, a_{p−2}, a_{p−3}, V (mass up to p − 4), s, z. -/
theorem bound_d_ge4 (e0 e1 e2 e3 V s z : ℚ)
    (n_e0 : 0 ≤ e0)
    (n_e1 : 0 ≤ e1)
    (n_e2 : 0 ≤ e2)
    (n_e3 : 0 ≤ e3)
    (n_V : 0 ≤ V)
    (n_s : 0 ≤ s)
    (h_A_p : (-1:ℚ)*e0 + ((-1:ℚ)/2)*e1 + ((-1:ℚ)/3)*e2 + ((-1:ℚ)/4)*e3 + ((-1:ℚ)/5)*V + (1:ℚ)*s ≤ (0:ℚ))
    (h_AL : (2:ℚ)*e1 + ((3:ℚ)/2)*e2 + ((4:ℚ)/3)*e3 + (1:ℚ)*V + (-1:ℚ)*s ≤ (1:ℚ))
    (h_BR_1 : (1:ℚ)*e0 + (-1:ℚ)*e1 + (-1:ℚ)*e2 + (-1:ℚ)*e3 + (-1:ℚ)*V ≤ (0:ℚ))
    (h_BR_2 : ((1:ℚ)/2)*e0 + (1:ℚ)*e1 + (-1:ℚ)*e2 + (-1:ℚ)*e3 + (-1:ℚ)*V ≤ (0:ℚ))
    (h_BR_3 : ((1:ℚ)/3)*e0 + ((1:ℚ)/2)*e1 + (1:ℚ)*e2 + (-1:ℚ)*e3 + (-1:ℚ)*V ≤ (0:ℚ))
    (h_cap0 : (1:ℚ)*e0 + (-1:ℚ)*s ≤ (0:ℚ))
    (h_cap1 : (1:ℚ)*e1 + (-1:ℚ)*s ≤ (0:ℚ))
    (h_cap2 : (1:ℚ)*e2 + (-1:ℚ)*s ≤ (0:ℚ))
    (h_cap3 : (1:ℚ)*e3 + (-1:ℚ)*s ≤ (0:ℚ))
    (h_Q__0 : (1:ℚ)*e0 + (1:ℚ)*e1 + (1:ℚ)*e2 + (1:ℚ)*e3 + (1:ℚ)*V ≤ (1:ℚ))
    (h_zA : (1:ℚ)*e0 + (-1:ℚ)*s + (1:ℚ)*z ≤ (0:ℚ)) :
    z ≤ ((2792:ℚ)/8461) := by
  linarith

theorem all_bounds_le_third : (1:ℚ)/5 ≤ 1/3 ∧ (5:ℚ)/17 ≤ 1/3 ∧ (110:ℚ)/333 ≤ 1/3 ∧ (2792:ℚ)/8461 ≤ 1/3 := by
  norm_num

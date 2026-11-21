import PacketTwoLayer.Main

namespace PacketTwoLayer

/-- Every state of the instance `a₀`, `b₀` with 11 players has makespan at least 5, so its optimum is 5. -/
theorem opt₀_ge (qs : List (ℕ × ℕ)) (hqs : ∀ p ∈ qs, p.1 < a₀.length ∧ p.2 < b₀.length)
    (hlen : qs.length = 11) : 5 ≤ makespan a₀ b₀ qs := by
  have h := three_mul_makespan_le a₀ b₀ (by decide) (by decide) eq₀ qs eq₀_valid.2 hqs
    (by rw [hlen, eq₀_valid.1]) eq₀_ufr
  rw [eq₀_makespan] at h
  omega

/-- The instance `a₀`, `b₀` with 11 players has a UFR equilibrium of makespan 7, and its optimal makespan is 5. -/
theorem poa_eq_seven_fifths :
    UFR a₀ b₀ eq₀ ∧ makespan a₀ b₀ eq₀ = 7 ∧ makespan a₀ b₀ opt₀ = 5 ∧
      ∀ qs : List (ℕ × ℕ), (∀ p ∈ qs, p.1 < a₀.length ∧ p.2 < b₀.length) → qs.length = 11 →
        makespan a₀ b₀ opt₀ ≤ makespan a₀ b₀ qs :=
  ⟨eq₀_ufr, eq₀_makespan, opt₀_makespan, fun qs hqs hlen => opt₀_makespan ▸ opt₀_ge qs hqs hlen⟩

end PacketTwoLayer

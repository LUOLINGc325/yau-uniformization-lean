import Yau.Proofs.P04GrowthAlgebra

noncomputable section
open Filter
open scoped Topology BigOperators

namespace Yau.Proofs.P04Aux

/-- Pointwise summability and the source's zero-based factor two bound. -/
theorem summable_and_tsum_le_geometric {a c : ℕ → ℝ} {E : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hc : ∀ i, 0 ≤ c i)
    (hbound : ∀ i, c i*a i ≤ (1/2 : ℝ)^i*E) :
    Summable (fun i => c i*a i) ∧ (∑' i, c i*a i) ≤ 2*E := by
  have hmajor : HasSum (fun i : ℕ => (1/2 : ℝ)^i*E) (2*E) := geometric_half_hasSum.mul_right E
  have hs : Summable (fun i => c i*a i) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hc i) (ha i)) hbound hmajor.summable
  exact ⟨hs,(hs.tsum_le_tsum hbound hmajor.summable).trans_eq hmajor.tsum_eq⟩

/-- Positivity uses one member of the same nonvanishing family. -/
theorem weighted_tsum_pos {a c : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hc : ∀ i, 0 < c i)
    (hs : Summable (fun i => c i*a i)) (hpos : ∃ i, 0 < a i) :
    0 < ∑' i, c i*a i := by
  obtain ⟨i,hi⟩ := hpos
  exact (mul_pos (hc i) hi).trans_le (hs.le_tsum i (fun j _ => mul_nonneg (hc j).le (ha j)))

/-- The common coefficient sequence and growth envelopes give a bound for
that same series, without changing either the sections or coefficients. -/
theorem weighted_series_of_exponential_bounds {a c B : ℕ → ℝ} {E : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hc : ∀ i, 0 ≤ c i) (hE : 0 ≤ E)
    (haB : ∀ i, a i ≤ Real.exp (B i)*E)
    (hcB : ∀ i, c i*Real.exp (B i) ≤ (1/2 : ℝ)^i) :
    Summable (fun i => c i*a i) ∧ (∑' i, c i*a i) ≤ 2*E := by
  apply summable_and_tsum_le_geometric ha hc
  intro i
  calc
    c i*a i ≤ c i*(Real.exp (B i)*E) := mul_le_mul_of_nonneg_left (haB i) (hc i)
    _ = (c i*Real.exp (B i))*E := by ring
    _ ≤ (1/2 : ℝ)^i*E := mul_le_mul_of_nonneg_right (hcB i) hE

end Yau.Proofs.P04Aux

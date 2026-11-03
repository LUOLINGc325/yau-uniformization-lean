import Yau.Proofs.Y03Windows
import Yau.Proofs.Y03SVD

/-! Both adjacent regular steps share one actual window-scale upper bound. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem adjacent_regular_rate_bounds (Q : ℕ → ℝ) (N L : ℕ) (M hm scale K eps b c : ℝ)
    (hM : 0 ≤ M) (hb : 0 < b) (hc : 0 < c) (j₀ : ℕ) (hj₀ : L + N ≤ j₀)
    (hQmono : MonotoneOn Q (Set.Ici L)) (hQlower : ∀ j, L ≤ j → c ≤ Q j)
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E) (hweights : WeightEstimates Q N M hm scale K eps b j₀ (rate F tk E))
    (k : ℕ) (hreg : Regular Q N M (macroAt Q N M hm j₀ k))
    (hreg' : Regular Q N M (macroAt Q N M hm j₀ (k + 1))) :
    (∀ i, 0 ≤ rate F tk E k i ∧ rate F tk E k i ≤
      (b⁻¹ * Real.exp M) * Q (macroAt Q N M hm j₀ k)) ∧
    (∀ i, 0 ≤ rate F tk E (k + 1) i ∧ rate F tk E (k + 1) i ≤
      (b⁻¹ * Real.exp M) * Q (macroAt Q N M hm j₀ k)) := by
  let j := macroAt Q N M hm j₀ k
  have hj : L + N ≤ j := hj₀.trans (macroAt_mem Q N M hm j₀ k).1
  have hQpos (r : ℕ) (hr : L ≤ r) : 0 < Q r := hc.trans_le (hQlower r hr)
  have hcomp := (regular_local_comparability hreg (by omega) (by omega) hQmono hQpos).2
  have hq : 0 ≤ Q j := (hQpos j (by omega)).le
  have hqscale : Q j ≤ Real.exp M * Q j := by
    exact (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (Real.one_le_exp_iff.2 hM) hq)
  have hQnext : Q (macroAt Q N M hm j₀ (k + 1)) ≤ Real.exp M * Q j := by
    rcases macroAt_succ_eq_or Q N M hm j₀ k with hs | hn
    · simpa only [hs] using hqscale
    · simpa only [hn] using hcomp
  constructor
  · intro i
    refine ⟨rate_nonneg hE k i, ((hweights.1 k i hreg).2.1).trans ?_⟩
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hqscale (inv_pos.2 hb).le
  · intro i
    refine ⟨rate_nonneg hE (k + 1) i, ((hweights.1 (k + 1) i hreg').2.1).trans ?_⟩
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hQnext (inv_pos.2 hb).le

end Yau.Blueprint.Alignment.Y03Proof

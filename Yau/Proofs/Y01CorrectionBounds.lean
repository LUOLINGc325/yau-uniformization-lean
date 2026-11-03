import Yau.Proofs.Y01CorrectionData
import Yau.Proofs.Y01SqrtEnvelopes

/-! The original Y06 bound extends to its identity correction values on
all inactive indices, with one explicit sqrt-clock constant. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux

variable {n : ℕ}

theorem all_correction_sqrt_bounds
    {Fhat : ℕ → ComplexVector n → ComplexVector n} {D J : ℕ → Herm n}
    {w : ℕ → Fin n → ℝ} {active : ℕ → Prop} {d Dstar : ℕ} {s : ℕ → ℝ}
    {C : ℝ} {Q : JetData n}
    (hQ : RegularJetSolution Fhat D J w active d Dstar s C Q)
    (hs : ∀ k, 1 ≤ s k) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ k,
      (Q.correction k).coeffNorm + (Q.inverseJet k).coeffNorm ≤
        Real.exp (C' * Real.sqrt (s k)) := by
  let C' := max C (2 * (n : ℝ))
  have hC' : 0 ≤ C' := (by positivity : 0 ≤ 2 * (n : ℝ)).trans (le_max_right _ _)
  refine ⟨C', hC', ?_⟩
  intro k
  by_cases hk : active k
  · obtain ⟨hlinear, hdegree, hvolume, hiDegree, hiZero, hleft, hright, hforbidden,
      hmZero, hmLinear, hallowed, hauto, hmDegree, hmiDegree, hjac, hconj, hnorm⟩ := hQ.2 k hk
    have hsmall : (Q.correction k).coeffNorm + (Q.inverseJet k).coeffNorm ≤
        Real.exp (C * Real.sqrt (s k)) := by
      linarith [coeffNorm_nonneg (Q.model k), coeffNorm_nonneg (Q.inverseModel k)]
    exact hsmall.trans (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)))
  · obtain ⟨hq, hqi⟩ := hQ.1 k hk
    rw [hq, hqi, coeffNorm_id]
    have hroot := sqrt_one_le (hs k)
    have h := Real.add_one_le_exp (2 * (n : ℝ))
    have hstep : 2 * (n : ℝ) ≤ C' * Real.sqrt (s k) := by
      have hbase : 2 * (n : ℝ) ≤ C' := le_max_right _ _
      nlinarith
    exact (show (n : ℝ) + (n : ℝ) ≤ Real.exp (2 * (n : ℝ)) by linarith).trans
      (Real.exp_le_exp.2 hstep)

end Yau.Proofs.Y01Aux

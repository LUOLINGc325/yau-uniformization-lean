import Yau.Proofs.P06CylinderRegularityLinearJets

/-! Finite linear coordinate combinations preserve a common jet bound. -/
noncomputable section
open scoped ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg

theorem norm_weighted_iteratedFDeriv_le {E α : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype α]
    (U : E → α → ℝ) (hU : ∀ r, ContDiff ℝ ∞ (fun p => U p r))
    (ℓ C : α → ℝ) (L : ℝ) (m : ℕ) (p : E)
    (hBound : ∀ r, ‖iteratedFDeriv ℝ m (fun p => U p r) p‖ ≤ C r*L) :
    ‖iteratedFDeriv ℝ m (fun p => ∑ r, ℓ r*U p r) p‖ ≤ (∑ r, |ℓ r| * C r)*L := by
  classical
  have hSum : iteratedFDeriv ℝ m (fun p => ∑ r, ℓ r * U p r) p =
      ∑ r, ℓ r • iteratedFDeriv ℝ m (fun p => U p r) p := by
    change iteratedFDeriv ℝ m (fun p => ∑ r, ℓ r • U p r) p = _
    rw [iteratedFDeriv_fun_sum_apply (fun r _ =>
      ((hU r).const_smul (ℓ r)).contDiffAt.of_le (by simp))]
    apply Finset.sum_congr rfl
    intro r _
    exact iteratedFDeriv_const_smul_apply' ((hU r).contDiffAt.of_le (by simp))
  rw [hSum]
  calc
    _ ≤ ∑ r, ‖ℓ r • iteratedFDeriv ℝ m (fun p => U p r) p‖ := norm_sum_le _ _
    _ ≤ ∑ r, |ℓ r| * C r*L := by
      apply Finset.sum_le_sum
      intro r _
      rw [norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (hBound r) (abs_nonneg _)).trans_eq (by ring)
    _ = _ := (Finset.sum_mul _ _ _).symm

end Yau.NodeProofs.P06Aux.CylinderReg

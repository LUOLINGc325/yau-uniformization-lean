import Yau.LeafProofs.L10InteriorH2Base

/-! Constant coordinate differentiation loses exactly one order in the original tensor norm. -/

noncomputable section
open MeasureTheory
open scoped ContDiff Topology BigOperators

namespace Yau.LeafProofs

theorem elliptic_directional_jet_norm_le {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : ComplexVector n → F} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ u O) {x : ComplexVector n} (hx : x ∈ O)
    (i : RIdx n) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ u y (realVec i)) x‖ ≤
      ‖iteratedFDeriv ℝ (k + 1) u x‖ := by
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ u) x :=
    (hu.contDiffAt (hO.mem_nhds hx)).fderiv_right (by simp)
  have h := norm_iteratedFDeriv_clm_apply_const (c := realVec i) (n := k) hD (by simp)
  have hn : ‖realVec i‖ = 1 := by
    rw [← complexVector_realOrthonormalBasis_apply]
    exact (complexVector_realOrthonormalBasis n).norm_eq_one _
  simpa only [hn, one_mul, norm_iteratedFDeriv_fderiv] using h

theorem elliptic_directional_jet_sq_integrableOn {n k : ℕ}
    {u : ComplexVector n → ℂ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ u O)
    (hi : IntegrableOn (fun x => ‖iteratedFDeriv ℝ (k + 1) u x‖^2) O (lebesgueC n))
    (i : RIdx n) : IntegrableOn
      (fun x => ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ u y (realVec i)) x‖^2) O (lebesgueC n) := by
  have hv := elliptic_contDiffOn_directionalDerivative hO hu (realVec i)
  have hc : ContinuousOn (fun x => iteratedFDeriv ℝ k (fun y => fderiv ℝ u y (realVec i)) x) O := by
    intro x hx
    exact ((hv.contDiffAt (hO.mem_nhds hx)).differentiableAt_iteratedFDeriv
      (m := k) (by exact_mod_cast ENat.natCast_lt_top k)).continuousAt.continuousWithinAt
  apply hi.mono' ((hc.norm.pow 2).aestronglyMeasurable hO.measurableSet)
  filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (elliptic_directional_jet_norm_le hO hu hx i k) 2

theorem elliptic_product_jet_bound {n k : ℕ}
    {a : ComplexVector n → ℝ} {u : ComplexVector n → ℂ}
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    (ha : ContDiffOn ℝ ∞ a O) (hu : ContDiffOn ℝ ∞ u O)
    {x : ComplexVector n} (hx : x ∈ O) {A : ℝ} (hA : 0 ≤ A)
    (haBound : ∀ j ≤ k, ‖iteratedFDeriv ℝ j a x‖ ≤ A) :
    ‖iteratedFDeriv ℝ k (fun y => a y • u y) x‖ ≤
      (A * 2^k) * ∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ j u x‖ := by
  let S : ℝ := ∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ j u x‖
  have huBound (j : ℕ) (hj : j ≤ k) : ‖iteratedFDeriv ℝ j u x‖ ≤ S :=
    Finset.single_le_sum (s := Finset.range (k + 1))
      (f := fun l => ‖iteratedFDeriv ℝ l u x‖)
      (fun l _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
  have hprod := norm_iteratedFDerivWithin_smul_le ha hu hO.uniqueDiffOn hx (n := k) (by simp)
  simp_rw [iteratedFDerivWithin_of_isOpen _ hO hx] at hprod
  have hsum : (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ)) = 2^k := by
    exact_mod_cast Nat.sum_range_choose k
  calc
    _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * A * S := by
      apply hprod.trans
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
      gcongr
      · exact haBound j hjk
      · exact huBound (k - j) (by omega)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
      dsimp only [S]
      ring

end Yau.LeafProofs

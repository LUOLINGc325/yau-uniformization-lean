import Yau.LeafProofs.L10InteriorCommutator

/-! One-letter derivatives control the full next tensor, with a dimension-only factor. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff Topology

namespace Yau.LeafProofs

theorem linear_norm_le_basis_sum {ι E F : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (b : OrthonormalBasis ι ℝ E) (L : E →L[ℝ] F) :
    ‖L‖ ≤ ∑ i, ‖L (b i)‖ := by
  classical
  apply L.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro x
  have heq : L x = ∑ i, b.repr x i • L (b i) := by
    nth_rw 1 [← b.sum_repr x]
    rw [map_sum]
    simp only [map_smul]
  rw [heq]
  calc
    _ ≤ ∑ i, ‖b.repr x i • L (b i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖x‖ * ‖L (b i)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [b.repr_apply_apply]
      exact (norm_inner_le_norm _ _).trans_eq (by rw [b.norm_eq_one, one_mul])
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem multilinear_linear_output_norm_sq_le {ι D E F : Type*} [Fintype ι]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (b : OrthonormalBasis ι ℝ E) {k : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => D) (E →L[ℝ] F)) :
    ‖T‖^2 ≤ (Fintype.card ι : ℝ) *
      ∑ i, ‖(ContinuousLinearMap.apply ℝ F (b i)).compContinuousMultilinearMap T‖^2 := by
  classical
  let T' (i : ι) := (ContinuousLinearMap.apply ℝ F (b i)).compContinuousMultilinearMap T
  have hnorm : ‖T‖ ≤ ∑ i, ‖T' i‖ := by
    apply T.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    intro m
    calc
      _ ≤ ∑ i, ‖T m (b i)‖ := linear_norm_le_basis_sum b (T m)
      _ ≤ ∑ i, ‖T' i‖ * ∏ j, ‖m j‖ := by
        apply Finset.sum_le_sum
        intro i _
        exact (T' i).le_opNorm m
      _ = _ := (Finset.sum_mul _ _ _).symm
  calc
    ‖T‖^2 ≤ (∑ i, ‖T' i‖)^2 := pow_le_pow_left₀ (norm_nonneg T) hnorm 2
    _ ≤ _ := by simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖T' i‖)

theorem elliptic_successor_jet_sq_le {n k : ℕ}
    {u : ComplexVector n → ℂ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ u O) {x : ComplexVector n} (hx : x ∈ O) :
    ‖iteratedFDeriv ℝ (k + 1) u x‖^2 ≤ (Fintype.card (RIdx n) : ℝ) *
      ∑ i, ‖iteratedFDeriv ℝ k (ellipticPartial u i) x‖^2 := by
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ u) x :=
    (hu.contDiffAt (hO.mem_nhds hx)).fderiv_right (by simp)
  have heq (i : RIdx n) :
      (ContinuousLinearMap.apply ℝ ℂ (realVec i)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ k (fderiv ℝ u) x) = iteratedFDeriv ℝ k (ellipticPartial u i) x := by
    change _ = iteratedFDeriv ℝ k (fun y => fderiv ℝ u y (realVec i)) x
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using
      ((ContinuousLinearMap.apply ℝ ℂ (realVec i)).iteratedFDeriv_comp_left hD
        (i := k) (by simp)).symm
  have h := multilinear_linear_output_norm_sq_le (complexVector_realOrthonormalBasis n)
    (iteratedFDeriv ℝ k (fderiv ℝ u) x)
  simpa only [norm_iteratedFDeriv_fderiv, complexVector_realOrthonormalBasis_apply, heq] using h

end Yau.LeafProofs

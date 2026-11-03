import Yau.Geometry.Calculus

open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {ι : Type*} [DecidableEq ι]

/-- An explicit affine chart of projective directions. Exactly one
coordinate is fixed to one and all other coordinates are free. -/
def projectiveCoordinates (pivot : ι) (w : {i : ι // i ≠ pivot} → ℂ) : ι → ℂ :=
  fun i => if h : i = pivot then 1 else w ⟨i, h⟩

@[simp]
theorem projectiveCoordinates_pivot (pivot : ι) (w : {i : ι // i ≠ pivot} → ℂ) :
    projectiveCoordinates pivot w pivot = 1 := by
  simp [projectiveCoordinates]

theorem exists_projectiveCoordinates (v : ι → ℂ) (hv : v ≠ 0) :
    ∃ (pivot : ι) (w : {i : ι // i ≠ pivot} → ℂ),
      v pivot ≠ 0 ∧ v = v pivot • projectiveCoordinates pivot w := by
  classical
  have hex : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  obtain ⟨pivot, hp⟩ := hex
  refine ⟨pivot, fun i => v i.1 / v pivot, hp, ?_⟩
  funext i
  by_cases hi : i = pivot
  · subst i
    simp only [Pi.smul_apply, smul_eq_mul, projectiveCoordinates_pivot, mul_one]
  · simp only [Pi.smul_apply, smul_eq_mul, projectiveCoordinates, dif_neg hi]
    exact (mul_div_cancel₀ (v i) hp).symm.trans (by ring)

theorem projectiveCoordinates_differentiable [Fintype ι] (pivot : ι) :
    Differentiable ℝ (projectiveCoordinates pivot) := by
  apply differentiable_pi.mpr
  intro i
  by_cases hi : i = pivot
  · simp only [projectiveCoordinates, dif_pos hi]
    exact differentiable_const 1
  · simp only [projectiveCoordinates, dif_neg hi]
    exact differentiable_apply (⟨i, hi⟩ : {l : ι // l ≠ pivot})

theorem projectiveParameters_finrank [Fintype ι] (pivot : ι) :
    Module.finrank ℝ ({i : ι // i ≠ pivot} → ℂ) = (Fintype.card ι - 1) * 2 := by
  simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex,
    Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [Fintype.card_subtype_compl (fun i : ι => i = pivot)]
  simp only [Fintype.card_unique]

theorem linearFunctional_coordinates {n : ℕ}
    (ξ : ComplexVector n →ₗ[ℂ] ℂ) (v : ComplexVector n) :
    ξ v = ∑ i : Fin n, ξ (stdVec i) * v i := by
  have hv : (∑ i : Fin n, v i • stdVec i) = v := by
    ext j
    simp [stdVec, PiLp.single_apply, Pi.single_apply, Finset.sum_apply', PiLp.smul_apply, eq_comm]
  calc
    ξ v = ξ (∑ i : Fin n, v i • stdVec i) := congrArg ξ hv.symm
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, smul_eq_mul, mul_comm]

/-- A proper finite span has a nonzero annihilator in one of the explicit
projective charts, with the original complex linear pairing. -/
theorem exists_projective_annihilator {n m : ℕ} (V : Fin m → ComplexVector n)
    (hV : Submodule.span ℂ (range V) ≠ ⊤) :
    ∃ (pivot : Fin n) (w : {i : Fin n // i ≠ pivot} → ℂ),
      ∀ j, (∑ i, projectiveCoordinates pivot w i * V j i) = 0 := by
  classical
  obtain ⟨ξ, hξ, hker⟩ := (Submodule.span ℂ (range V)).exists_le_ker_of_lt_top
    (lt_top_iff_ne_top.mpr hV)
  let q : Fin n → ℂ := fun i => ξ (stdVec i)
  have hq : q ≠ 0 := by
    intro hq
    apply hξ
    ext v
    rw [linearFunctional_coordinates]
    simp only [show ∀ i, ξ (stdVec i) = 0 from fun i => congrFun hq i,
      zero_mul, Finset.sum_const_zero, LinearMap.zero_apply]
  obtain ⟨pivot, w, hp, heq⟩ := exists_projectiveCoordinates q hq
  refine ⟨pivot, w, ?_⟩
  intro j
  have hz : ξ (V j) = 0 := hker (Submodule.subset_span (mem_range_self j))
  have he : q pivot * (∑ i, projectiveCoordinates pivot w i * V j i) = 0 := by
    rw [Finset.mul_sum]
    calc
      (∑ i, q pivot * (projectiveCoordinates pivot w i * V j i)) =
          ∑ i, q i * V j i := by
        apply Finset.sum_congr rfl
        intro i _
        have hi := congrFun heq i
        change q i = q pivot * projectiveCoordinates pivot w i at hi
        rw [← mul_assoc, ← hi]
      _ = ξ (V j) := (linearFunctional_coordinates ξ (V j)).symm
      _ = 0 := hz
  exact (mul_eq_zero.mp he).resolve_left hp

end Yau.NodeProofs.P03Aux

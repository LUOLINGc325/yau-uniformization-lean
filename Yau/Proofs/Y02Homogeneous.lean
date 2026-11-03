import Yau.Proofs.Y02Algebra

/-! Homogeneous polynomial vector fields and their divergence. -/

noncomputable section

open scoped BigOperators

namespace Yau.Proofs.Y02Aux

open MvPolynomial

variable {n : ℕ}

/-- Homogeneous vector polynomials, as a submodule of polynomial maps. -/
def homogeneousFields (n m : ℕ) : Submodule ℂ (PolyMap n) where
  carrier := {P | ∀ i, (P i).IsHomogeneous m}
  zero_mem' := fun i => isHomogeneous_zero _ _ _
  add_mem' hP hQ i := (hP i).add (hQ i)
  smul_mem' c P hP i := by
    simpa only [Pi.smul_apply, smul_eq_C_mul] using (hP i).C_mul c

/-- Formal divergence of a polynomial vector field. -/
def divergence (n : ℕ) : PolyMap n →ₗ[ℂ] MvPolynomial (Fin n) ℂ where
  toFun P := ∑ i, pderiv i (P i)
  map_add' P Q := by simp [Finset.sum_add_distrib]
  map_smul' c P := by simp [← Finset.smul_sum]

/-- The homogeneous field whose time map is `shear l v m`. -/
def shearField (l v : Fin n → ℂ) (m : ℕ) : PolyMap n :=
  fun i => C (v i) * linearForm l ^ m

/-- All degree-`m` shear fields with the required orthogonality relation. -/
def shearFields (n m : ℕ) : Set (PolyMap n) :=
  {P | ∃ l v : Fin n → ℂ, (∑ i, l i * v i) = 0 ∧ P = shearField l v m}

theorem linearForm_homogeneous (l : Fin n → ℂ) : (linearForm l).IsHomogeneous 1 := by
  exact IsHomogeneous.sum _ _ _ fun i hi => isHomogeneous_C_mul_X _ _

theorem shearField_homogeneous (l v : Fin n → ℂ) (m : ℕ) :
    shearField l v m ∈ homogeneousFields n m := by
  intro i
  have h := ((linearForm_homogeneous l).pow m).C_mul (v i)
  simpa only [one_mul, shearField] using h

theorem pderiv_linearForm (l : Fin n → ℂ) (i : Fin n) :
    pderiv i (linearForm l) = C (l i) := by
  classical
  simp [linearForm, pderiv_X, Pi.single_apply]

theorem divergence_shearField (l v : Fin n → ℂ) (m : ℕ) :
    divergence n (shearField l v m) =
      C ((m : ℂ) * ∑ i, l i * v i) * linearForm l ^ (m - 1) := by
  change (∑ i, pderiv i (C (v i) * linearForm l ^ m)) = _
  simp only [pderiv_C_mul, pderiv_pow, pderiv_linearForm]
  calc
    _ = (∑ i, C ((m : ℂ) * (l i * v i))) * linearForm l ^ (m - 1) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [map_mul, map_natCast]
      ring
    _ = _ := by rw [Finset.mul_sum, map_sum]

theorem shearField_divergence_zero (l v : Fin n → ℂ) (m : ℕ)
    (hlv : ∑ i, l i * v i = 0) : divergence n (shearField l v m) = 0 := by
  rw [divergence_shearField, hlv]
  simp

theorem shearFields_span_le (m : ℕ) :
    Submodule.span ℂ (shearFields n m) ≤
      homogeneousFields n m ⊓ LinearMap.ker (divergence n) := by
  apply Submodule.span_le.mpr
  rintro P ⟨l, v, hlv, rfl⟩
  exact ⟨shearField_homogeneous l v m, shearField_divergence_zero l v m hlv⟩

theorem homogeneous_jetEq_zero {m d : ℕ} (hmd : d < m) {P : PolyMap n}
    (hP : P ∈ homogeneousFields n m) : PolyMap.JetEq P 0 d := by
  intro i a ha
  rw [hP i |>.coeff_eq_zero (show a.degree ≠ m from ne_of_lt (lt_of_le_of_lt ha hmd))]
  simp

/-- A degree-`m` shear does not change any coefficient of degree less than `m`. -/
theorem shear_jetEq_id (l v : Fin n → ℂ) (m d : ℕ) (c : ℂ) (hmd : d < m) :
    PolyMap.JetEq (shear l v m c) PolyMap.id d := by
  intro i a ha
  change (X i + C (c * v i) * linearForm l ^ m).coeff a = (X i).coeff a
  have hhom : (C (c * v i) * linearForm l ^ m).IsHomogeneous m := by
    simpa only [one_mul] using ((linearForm_homogeneous l).pow m).C_mul (c * v i)
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    hhom.coeff_eq_zero (show a.degree ≠ m from ne_of_lt (lt_of_le_of_lt ha hmd)),
    add_zero]

theorem shear_fixesZero (l v : Fin n → ℂ) (m : ℕ) (c : ℂ) (hm : 0 < m) :
    (shear l v m c).FixesZero := by
  intro i
  have h := shear_jetEq_id l v m 0 c hm i 0 (by simp)
  simpa [PolyMap.id, coeff_X] using h

theorem shear_degree_le (l v : Fin n → ℂ) (m : ℕ) (c : ℂ) :
    (shear l v m c).degree ≤ max 1 m := by
  unfold PolyMap.degree
  apply Finset.sup_le
  intro i hi
  apply (totalDegree_add _ _).trans
  apply max_le_max
  · simp
  · have hhom := ((linearForm_homogeneous l).pow m).C_mul (c * v i)
    simpa only [one_mul] using hhom.totalDegree_le

set_option backward.isDefEq.respectTransparency false in
theorem shear_jacDet (l v : Fin n → ℂ) (m : ℕ) (c : ℂ)
    (hlv : ∑ i, l i * v i = 0) : (shear l v m c).jacDet = 1 := by
  let u : Fin n → MvPolynomial (Fin n) ℂ := fun i => C (c * v i)
  let w : Fin n → MvPolynomial (Fin n) ℂ :=
    fun j => (m : MvPolynomial (Fin n) ℂ) * linearForm l ^ (m - 1) * C (l j)
  have hmatrix : (fun i j => pderiv j (shear l v m c i) :
      Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) ℂ)) =
      1 + Matrix.replicateCol Unit u * Matrix.replicateRow Unit w := by
    apply Matrix.ext
    intro i j
    change pderiv j (shear l v m c i) =
      (if i = j then 1 else 0) + ∑ _k : Unit, u i * w j
    simp only [Fintype.sum_unique, shear, u, w, map_add, pderiv_C_mul, pderiv_pow,
      pderiv_linearForm, pderiv_X, Pi.single_apply]
  unfold PolyMap.jacDet
  rw [hmatrix, Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hdot : w ⬝ᵥ u = 0 := by
    change (∑ i, ((m : MvPolynomial (Fin n) ℂ) * linearForm l ^ (m - 1) * C (l i)) *
      C (c * v i)) = 0
    calc
      _ = (m : MvPolynomial (Fin n) ℂ) * linearForm l ^ (m - 1) *
          C (c * ∑ i, l i * v i) := by
        simp only [Finset.mul_sum, map_sum, map_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [hlv]; simp
  rw [hdot, add_zero]

end Yau.Proofs.Y02Aux

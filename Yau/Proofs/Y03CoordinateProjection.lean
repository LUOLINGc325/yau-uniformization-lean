import Yau.Blueprint.Alignment

/-! Coordinate subspaces and their actual orthogonal coordinate projections. -/

open scoped Matrix

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

def coordinateSubspace (s : Finset (Fin n)) : Submodule ℂ (ComplexVector n) where
  carrier := {v | ∀ i, i ∉ s → v i = 0}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw i hi; change v i + w i = 0; rw [hv i hi, hw i hi, add_zero]
  smul_mem' := by intro c v hv i hi; change c * v i = 0; rw [hv i hi, mul_zero]

def coordinateProjection (s : Finset (Fin n)) : ComplexVector n →L[ℂ] ComplexVector n :=
  Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
    (Matrix.diagonal (fun i => if i ∈ s then 1 else 0))

theorem coordinateProjection_apply (s : Finset (Fin n)) (v : ComplexVector n) (i : Fin n) :
    coordinateProjection s v i = if i ∈ s then v i else 0 := by
  change ((Matrix.diagonal (fun j => if j ∈ s then (1 : ℂ) else 0)) *ᵥ WithLp.ofLp v) i = _
  rw [Matrix.mulVec_diagonal]
  split_ifs <;> simp

theorem coordinateProjection_mem (s : Finset (Fin n)) (v : ComplexVector n) :
    coordinateProjection s v ∈ coordinateSubspace s := by
  intro i hi
  rw [coordinateProjection_apply, ite_eq_right hi]

theorem coordinateProjection_eq_self {s : Finset (Fin n)} {v : ComplexVector n}
    (hv : v ∈ coordinateSubspace s) : coordinateProjection s v = v := by
  ext i
  rw [coordinateProjection_apply]
  split_ifs with hi
  · rfl
  · exact (hv i hi).symm

theorem coordinateProjection_comp {s t : Finset (Fin n)} (hst : s ⊆ t) :
    (coordinateProjection s).comp (coordinateProjection t) = coordinateProjection s := by
  ext v i
  simp only [ContinuousLinearMap.comp_apply, coordinateProjection_apply]
  by_cases hi : i ∈ s
  · simp only [hi, hst hi, ite_true]
  · simp only [hi, ite_false]

theorem coordinateProjection_norm_sq (s : Finset (Fin n)) (v : ComplexVector n) :
    ‖coordinateProjection s v‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [coordinateProjection_apply]
  simp_rw [apply_ite (fun z : ℂ => ‖z‖ ^ 2), norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  simpa only [Finset.univ_inter] using Finset.sum_ite_mem Finset.univ s (fun i => ‖v i‖ ^ 2)

theorem coordinateProjection_norm_le (s : Finset (Fin n)) (v : ComplexVector n) :
    ‖coordinateProjection s v‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [coordinateProjection_norm_sq, EuclideanSpace.norm_sq_eq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)

theorem coordinateProjection_opNorm_le (s : Finset (Fin n)) : ‖coordinateProjection s‖ ≤ 1 := by
  refine (coordinateProjection s).opNorm_le_bound zero_le_one ?_
  intro v
  simpa only [one_mul] using coordinateProjection_norm_le s v

theorem coordinateProjection_compl (s : Finset (Fin n)) :
    ContinuousLinearMap.id ℂ (ComplexVector n) - coordinateProjection s = coordinateProjection sᶜ := by
  ext v i
  change v i - coordinateProjection s v i = coordinateProjection sᶜ v i
  simp only [coordinateProjection_apply, Finset.mem_compl]
  by_cases hi : i ∈ s <;> simp [hi]

def coordinateProjectionOnto (s : Finset (Fin n)) :
    ComplexVector n →L[ℂ] coordinateSubspace s :=
  (coordinateProjection s).codRestrict (coordinateSubspace s) (coordinateProjection_mem s)

theorem coordinateProjectionOnto_right_inverse (s : Finset (Fin n)) :
    (coordinateProjectionOnto s).comp (coordinateSubspace s).subtypeL =
      ContinuousLinearMap.id ℂ (coordinateSubspace s) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Subtype.ext
  exact coordinateProjection_eq_self v.property

end Yau.Blueprint.Alignment.Y03Proof

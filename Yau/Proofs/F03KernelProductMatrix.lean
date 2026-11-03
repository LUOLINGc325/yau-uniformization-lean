import Yau.Proofs.F03KernelProductIndices

/-! The true half block-diagonal product matrix, with its actual quadratic form. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

def kernelProductMatrix {n : ℕ} (A B : Mat n) : Mat (n+n) := fun i j =>
  match (kernelRealIndexSumEquiv n).symm i,(kernelRealIndexSumEquiv n).symm j with
  | Sum.inl i,Sum.inl j => (1/2 : ℝ)*A i j
  | Sum.inr i,Sum.inr j => (1/2 : ℝ)*B i j
  | _,_ => 0

theorem kernelProductMatrix_left_left {n : ℕ} (A B : Mat n) (i j : RIdx n) :
    kernelProductMatrix A B (kernelRealIndexLeft n i) (kernelRealIndexLeft n j)=(1/2 : ℝ)*A i j := by
  simp only [kernelProductMatrix,kernelRealIndexSumEquiv_symm_left]

theorem kernelProductMatrix_left_right {n : ℕ} (A B : Mat n) (i j : RIdx n) :
    kernelProductMatrix A B (kernelRealIndexLeft n i) (kernelRealIndexRight n j)=0 := by
  simp only [kernelProductMatrix,kernelRealIndexSumEquiv_symm_left,kernelRealIndexSumEquiv_symm_right]

theorem kernelProductMatrix_right_left {n : ℕ} (A B : Mat n) (i j : RIdx n) :
    kernelProductMatrix A B (kernelRealIndexRight n i) (kernelRealIndexLeft n j)=0 := by
  simp only [kernelProductMatrix,kernelRealIndexSumEquiv_symm_left,kernelRealIndexSumEquiv_symm_right]

theorem kernelProductMatrix_right_right {n : ℕ} (A B : Mat n) (i j : RIdx n) :
    kernelProductMatrix A B (kernelRealIndexRight n i) (kernelRealIndexRight n j)=(1/2 : ℝ)*B i j := by
  simp only [kernelProductMatrix,kernelRealIndexSumEquiv_symm_right]

theorem kernelProductMatrix_quadratic {n : ℕ} (A B : Mat n) (v : RIdx (n+n) → ℝ) :
    (∑ i,∑ j,kernelProductMatrix A B i j*v i*v j)=
      (1/2 : ℝ)*((∑ i,∑ j,A i j*v (kernelRealIndexLeft n i)*v (kernelRealIndexLeft n j))+
        (∑ i,∑ j,B i j*v (kernelRealIndexRight n i)*v (kernelRealIndexRight n j))) := by
  simp_rw [sum_kernel_real_index n]
  simp only [kernelProductMatrix_left_left,kernelProductMatrix_left_right,
    kernelProductMatrix_right_left,kernelProductMatrix_right_right,zero_mul,
    Finset.sum_const_zero,add_zero,zero_add]
  rw [mul_add]
  congr 1 <;> simp only [Finset.mul_sum] <;>
    apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

theorem kernelProductMatrix_symm {n : ℕ} (A B : Mat n) (hA : A.IsSymm) (hB : B.IsSymm) :
    (kernelProductMatrix A B).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  obtain ⟨i,rfl⟩ := (kernelRealIndexSumEquiv n).surjective i
  obtain ⟨j,rfl⟩ := (kernelRealIndexSumEquiv n).surjective j
  rcases i with i|i <;> rcases j with j|j <;>
    simp only [kernelRealIndexSumEquiv_inl,kernelRealIndexSumEquiv_inr,
      kernelProductMatrix_left_left,kernelProductMatrix_left_right,
      kernelProductMatrix_right_left,kernelProductMatrix_right_right]
  · rw [hA.apply i j]
  · rw [hB.apply i j]

theorem kernelProductMatrix_quadratic_bounds {n : ℕ} (A B : Mat n)
    (la ua lb ub : ℝ)
    (hA : ∀ v : RIdx n → ℝ,
      la*(∑ i,(v i)^2) ≤ ∑ i,∑ j,A i j*v i*v j ∧
      (∑ i,∑ j,A i j*v i*v j) ≤ ua*(∑ i,(v i)^2))
    (hB : ∀ v : RIdx n → ℝ,
      lb*(∑ i,(v i)^2) ≤ ∑ i,∑ j,B i j*v i*v j ∧
      (∑ i,∑ j,B i j*v i*v j) ≤ ub*(∑ i,(v i)^2))
    (v : RIdx (n+n) → ℝ) :
    (min la lb/2)*(∑ i,(v i)^2) ≤ ∑ i,∑ j,kernelProductMatrix A B i j*v i*v j ∧
      (∑ i,∑ j,kernelProductMatrix A B i j*v i*v j) ≤ (max ua ub/2)*(∑ i,(v i)^2) := by
  have hAL := hA (fun i => v (kernelRealIndexLeft n i))
  have hBR := hB (fun i => v (kernelRealIndexRight n i))
  have hSL : 0 ≤ ∑ i,(v (kernelRealIndexLeft n i))^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hSR : 0 ≤ ∑ i,(v (kernelRealIndexRight n i))^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  rw [kernelProductMatrix_quadratic,sum_kernel_real_index n]
  constructor
  · have h1 := mul_le_mul_of_nonneg_right (min_le_left la lb) hSL
    have h2 := mul_le_mul_of_nonneg_right (min_le_right la lb) hSR
    nlinarith [hAL.1,hBR.1]
  · have h1 := mul_le_mul_of_nonneg_right (le_max_left ua ub) hSL
    have h2 := mul_le_mul_of_nonneg_right (le_max_right ua ub) hSR
    nlinarith [hAL.2,hBR.2]

end Yau.Proofs.F03Aux

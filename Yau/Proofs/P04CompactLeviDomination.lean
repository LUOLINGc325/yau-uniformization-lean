import Yau.Proofs.P04CompactQuadraticBounds

noncomputable section
open WithLp
open scoped Topology InnerProductSpace Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau
variable {n : ℕ}

theorem matrixQuadratic_add (A B : Matrix (Fin n) (Fin n) ℂ) (v : ComplexVector n) :
    matrixQuadratic (A+B) v=matrixQuadratic A v+matrixQuadratic B v := by
  simp only [matrixQuadratic,Matrix.add_mulVec,dotProduct_add,Complex.add_re]

theorem matrixQuadratic_matrix_real_smul (A : Matrix (Fin n) (Fin n) ℂ)
    (r : ℝ) (v : ComplexVector n) : matrixQuadratic (r • A) v=r*matrixQuadratic A v := by
  unfold matrixQuadratic
  rw [Matrix.smul_mulVec,dotProduct_smul]
  simp only [smul_eq_mul,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

theorem matrixQuadratic_nonneg_iff {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    A.PosSemidef ↔ ∀ v : ComplexVector n, 0 ≤ matrixQuadratic A v := by
  constructor
  · intro H v
    exact (Complex.nonneg_iff.mp (H.dotProduct_mulVec_nonneg (fun i => v i))).1
  · intro H
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hA
    intro x
    have hre := H (toLp 2 x)
    change 0 ≤ (star x ⬝ᵥ A *ᵥ x).re at hre
    have him := congrArg Complex.im (hA.star_dotProduct_mulVec_comm x x)
    simp only [Complex.star_def,Complex.conj_im] at him
    exact Complex.nonneg_iff.mpr ⟨hre,by linarith⟩

/-- One scalar dominates the entire compact family of actual Hermitian
errors against a continuous strictly positive family. -/
theorem compact_posDef_dominates_error {α : Type*} [TopologicalSpace α] [CompactSpace α]
    (A E : α → Matrix (Fin n) (Fin n) ℂ) (hA : Continuous A) (hE : Continuous E)
    (hpos : ∀ a, (A a).PosDef) (hHerm : ∀ a, (E a).IsHermitian) :
    ∃ k : ℝ, 1 ≤ k ∧ ∀ a, (((k-1 : ℝ) : ℂ) • A a+E a).PosSemidef := by
  obtain ⟨δ,hδ,hδbound⟩ := compact_posDef_uniform_lower_bound A hA hpos
  obtain ⟨C,hC,hCbound⟩ := compact_matrix_uniform_quadratic_bound E hE
  refine ⟨1+C/δ,by linarith [div_nonneg hC hδ.le],fun a => ?_⟩
  have heq : (1+C/δ)-1=C/δ := by ring
  rw [heq]
  apply (matrixQuadratic_nonneg_iff
    (((hpos a).posSemidef.smul (div_nonneg hC hδ.le)).isHermitian.add (hHerm a))).mpr
  intro v
  rw [matrixQuadratic_add,matrixQuadratic_matrix_real_smul]
  have Hδ := mul_le_mul_of_nonneg_left (hδbound a v) (div_nonneg hC hδ.le)
  have HE := (abs_le.mp (hCbound a v)).1
  have hcancel : C/δ*(δ*‖v‖^2)=C*‖v‖^2 := by field_simp
  rw [hcancel] at Hδ
  linarith

end Yau.Proofs.P04Aux

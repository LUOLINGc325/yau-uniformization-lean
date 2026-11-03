import Yau.LeafProofs.L05TraceEllipticity

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

theorem sym_coe_formula {n : ℕ} (A : Mat n) :
    (sym A : Mat n)=(1/2:ℝ) • (A+A.transpose) := by
  change (⅟2:ℝ) • (A+star A)=(1/2:ℝ) • (A+A.transpose)
  congr 1
  · norm_num

theorem sym_transpose {n : ℕ} (A : Mat n) : sym A.transpose=sym A := by
  apply Subtype.ext
  rw [sym_coe_formula,sym_coe_formula,Matrix.transpose_transpose,add_comm]

theorem sym_single_flip {n : ℕ} (i j : RIdx n) :
    sym (Matrix.single i j (1:ℝ))=sym (Matrix.single j i 1) := by
  rw [← Matrix.transpose_single,sym_transpose]

theorem sym_eq_sum_basis {n : ℕ} (H : Sym n) :
    H=∑ i, ∑ j, (H : Mat n) i j • sym (Matrix.single i j (1:ℝ)) := by
  have he : sym (H : Mat n)=H :=
    Subtype.ext (IsSelfAdjoint.coe_selfAdjointPart_apply ℝ H.property)
  have hr : (H : Mat n)=∑ i, ∑ j, (H : Mat n) i j • Matrix.single i j (1:ℝ) := by
    simpa only [Matrix.smul_single,smul_eq_mul,mul_one] using Matrix.matrix_eq_sum_single (H : Mat n)
  calc
    H=sym (H : Mat n) := he.symm
    _=sym (∑ i, ∑ j, (H : Mat n) i j • Matrix.single i j (1:ℝ)) := by rw [← hr]
    _=_ := by simp only [sym,map_sum,map_smul]

def dualMatrix {n : ℕ} (l : Sym n →ₗ[ℝ] ℝ) : Sym n :=
  ⟨(fun i j => l (sym (Matrix.single i j (1:ℝ)))),by
    apply Matrix.isHermitian_iff_isSelfAdjoint.mp
    apply Matrix.IsHermitian.ext
    intro i j
    change l (sym (Matrix.single j i (1:ℝ)))=l (sym (Matrix.single i j 1))
    rw [sym_single_flip]⟩

theorem dualMatrix_apply {n : ℕ} (l : Sym n →ₗ[ℝ] ℝ) (H : Sym n) :
    l H=tracePair (dualMatrix l) H := by
  have hh := congrArg l (sym_eq_sum_basis H)
  simp only [map_sum,map_smul,smul_eq_mul] at hh
  rw [hh]
  have hsym (i j : RIdx n) : (H : Mat n) j i=(H : Mat n) i j := by
    simpa only [star_trivial] using (Matrix.isHermitian_iff_isSelfAdjoint.mpr H.property).apply i j
  change (∑ i, ∑ j, (H : Mat n) i j*l (sym (Matrix.single i j (1:ℝ)) ))=
    ∑ i, ∑ j, l (sym (Matrix.single i j (1:ℝ)))*(H : Mat n) j i
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hsym]
  exact mul_comm _ _

theorem tracePair_rankOne {n : ℕ} (A : Sym n) (v : RIdx n → ℝ) :
    tracePair A (rankOne v)=star v ⬝ᵥ ((A : Mat n)*ᵥ v) := by
  unfold tracePair
  rw [rankOne_coe]
  change (∑ i, ∑ j, (A : Mat n) i j*(v j*v i))=
    ∑ i, v i*(∑ j, (A : Mat n) i j*v j)
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end Yau.LeafProofs.L05Aux

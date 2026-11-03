import Yau.LeafProofs.L05DualMatrix

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

theorem dualMatrix_mem_slopeSet {n : ℕ} {ell L : ℝ} (l : Sym n →ₗ[ℝ] ℝ)
    (hl : ∀ v : RIdx n → ℝ, ell*(∑ i, (v i)^2) ≤ l (rankOne v) ∧
      l (rankOne v) ≤ L*(∑ i, (v i)^2)) : dualMatrix l ∈ slopeSet n ell L := by
  have hquad (v : RIdx n → ℝ) : ell*(∑ i, (v i)^2) ≤ star v ⬝ᵥ ((dualMatrix l : Mat n)*ᵥ v) ∧
      star v ⬝ᵥ ((dualMatrix l : Mat n)*ᵥ v) ≤ L*(∑ i, (v i)^2) := by
    have hh := hl v
    rw [dualMatrix_apply,tracePair_rankOne] at hh
    exact hh
  constructor
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · exact Matrix.isHermitian_iff_isSelfAdjoint.mpr ((dualMatrix l).property.sub
        (IsSelfAdjoint.smul (IsSelfAdjoint.all _) (IsSelfAdjoint.one _)))
    · intro v
      simpa only [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_sub,
        dotProduct_smul,star_trivial,smul_eq_mul,dotProduct,pow_two,Pi.sub_apply,Pi.smul_apply,
        mul_sub,mul_left_comm,mul_assoc,Finset.sum_sub_distrib,← Finset.mul_sum] using sub_nonneg.mpr (hquad v).1
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · exact Matrix.isHermitian_iff_isSelfAdjoint.mpr
        ((IsSelfAdjoint.smul (IsSelfAdjoint.all _) (IsSelfAdjoint.one _)).sub (dualMatrix l).property)
    · intro v
      simpa only [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_sub,
        dotProduct_smul,star_trivial,smul_eq_mul,dotProduct,pow_two,Pi.sub_apply,Pi.smul_apply,
        mul_sub,mul_left_comm,mul_assoc,Finset.sum_sub_distrib,← Finset.mul_sum] using sub_nonneg.mpr (hquad v).2

def chuSlope {n : ℕ} (F : Sym n → Point n → ℝ) (A : Sym n) (p : Point n) : Sym n :=
  dualMatrix (fderiv ℝ (fun N => F N p) A).toLinearMap

theorem chuSlope_apply {n : ℕ} (F : Sym n → Point n → ℝ) (A V : Sym n) (p : Point n) :
    fderiv ℝ (fun N => F N p) A V=tracePair (chuSlope F A p) V :=
  dualMatrix_apply _ V

theorem chuSlope_mem_slopeSet {n : ℕ} {E U : Set (Sym n)} {F : Sym n → Point n → ℝ}
    {ell L K beta : ℝ} (hF : ChuH1 E U F ell L K beta) {A : Sym n} (hA : A ∈ E)
    {p : Point n} (hp : p ∈ backward 1) : chuSlope F A p ∈ slopeSet n ell L := by
  apply dualMatrix_mem_slopeSet
  exact hF.2.2.2.1 A hA p hp

theorem chuSlope_norm_le {n : ℕ} {E U : Set (Sym n)} {F : Sym n → Point n → ℝ}
    {ell L K beta : ℝ} (hell : 0 ≤ ell) (hF : ChuH1 E U F ell L K beta)
    {A : Sym n} (hA : A ∈ E) {p : Point n} (hp : p ∈ backward 1) :
    ‖chuSlope F A p‖ ≤ (2*n)*L :=
  slopeSet_norm_le hell (chuSlope_mem_slopeSet hF hA hp)

theorem chuDerivative_bound {n : ℕ} {E U : Set (Sym n)} {F : Sym n → Point n → ℝ}
    {ell L K beta : ℝ} (hell : 0 ≤ ell) (hF : ChuH1 E U F ell L K beta)
    {A : Sym n} (hA : A ∈ E) {p : Point n} (hp : p ∈ backward 1) (V : Sym n) :
    |fderiv ℝ (fun N => F N p) A V| ≤ Real.sqrt (Fintype.card (RIdx n))*((2*n)*L)*‖V‖ := by
  rw [chuSlope_apply]
  exact (abs_trace_mul_le (chuSlope F A p : Mat n) (V : Mat n)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (chuSlope_norm_le hell hF hA hp)
      (Real.sqrt_nonneg _)) (norm_nonneg _))

end Yau.LeafProofs.L05Aux

import Yau.Proofs.F01MatrixComparison
import Yau.LeafProofs.L22LeviCalculus

/-! Actual Loewner inequalities recovered from real quadratic inequalities. -/
noncomputable section
open scoped Matrix ComplexOrder ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

theorem matrix_posSemidef_sub_iff_quadratic {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (B - A).PosSemidef ↔ ∀ v : Fin n → ℂ,
      (star v ⬝ᵥ (A *ᵥ v)).re ≤ (star v ⬝ᵥ (B *ᵥ v)).re := by
  constructor
  · intro h v
    have hr := (Complex.nonneg_iff.mp (h.dotProduct_mulVec_nonneg v)).1
    simpa only [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, sub_nonneg] using hr
  · intro h
    have hh := hB.sub hA
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hh
    intro v
    apply Complex.nonneg_iff.mpr
    refine ⟨?_, (hermitian_quadratic_im_zero hh v).symm⟩
    simpa only [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, sub_nonneg] using h v

theorem leviC_sandwich_of_quadratic (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (B : ℝ)
    (hb : ∀ v : ComplexVector n,
      |LeafProofs.L22Aux.complexLeviQuadratic f z v| ≤
        B * (star (WithLp.ofLp v) ⬝ᵥ (H *ᵥ WithLp.ofLp v)).re) :
    (leviC f z - ((-B : ℝ) : ℂ) • H).PosSemidef ∧
      ((B : ℂ) • H - leviC f z).PosSemidef := by
  have hs (b : ℝ) : ((b : ℂ) • H).IsHermitian :=
    hH.smul (show IsSelfAdjoint (b : ℂ) from Complex.conj_ofReal b)
  have hfH := LeafProofs.L22Aux.leviC_isHermitian hf
  constructor
  · apply (matrix_posSemidef_sub_iff_quadratic (hs (-B)) hfH).mpr
    intro v
    have h := (abs_le.mp (hb (WithLp.toLp 2 v))).1
    rw [← LeafProofs.L22Aux.leviC_quadratic_re hf] at h
    simpa only [WithLp.ofLp_toLp, Matrix.smul_mulVec, dotProduct_smul,
      smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, neg_mul] using h
  · apply (matrix_posSemidef_sub_iff_quadratic hfH (hs B)).mpr
    intro v
    have h := (abs_le.mp (hb (WithLp.toLp 2 v))).2
    rw [← LeafProofs.L22Aux.leviC_quadratic_re hf] at h
    simpa only [WithLp.ofLp_toLp, Matrix.smul_mulVec, dotProduct_smul,
      smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using h

end Yau.NodeProofs.F01Aux

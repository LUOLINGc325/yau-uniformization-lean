import Yau.Proofs.F01ScalarLeviEstimate
import Yau.Proofs.F01ConformalScaledCoefficient
import Yau.Proofs.F01ConformalGradientBound
import Yau.Proofs.F01LeviOrder

/-! The two-sided Levi bound for the actual conformal factor, with one
constant selected before all scales and actual points. -/
noncomputable section
open Set
open scoped ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem leviC_quadratic_abs_of_sandwich (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (a : ℝ)
    (hlo : (leviC f z - ((-a : ℝ) : ℂ) • H).PosSemidef)
    (hhi : ((a : ℂ) • H - leviC f z).PosSemidef) (v : ComplexVector n) :
    |LeafProofs.L22Aux.complexLeviQuadratic f z v| ≤
      a * (star (WithLp.ofLp v) ⬝ᵥ (H *ᵥ WithLp.ofLp v)).re := by
  have hs (b : ℝ) : ((b : ℂ) • H).IsHermitian :=
    hH.smul (show IsSelfAdjoint (b : ℂ) from Complex.conj_ofReal b)
  have hfH := LeafProofs.L22Aux.leviC_isHermitian hf
  have hl := (matrix_posSemidef_sub_iff_quadratic (hs (-a)) hfH).mp hlo (WithLp.ofLp v)
  have hh := (matrix_posSemidef_sub_iff_quadratic hfH (hs a)).mp hhi (WithLp.ofLp v)
  rw [LeafProofs.L22Aux.leviC_quadratic_re hf] at hl hh
  apply abs_le.mpr
  constructor
  · simpa only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, neg_mul] using hl
  · simpa only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hh

theorem conformalScalar_universal_levi_bound (C : ℝ) (hC : 0 < C) :
    ∃ B : ℝ, 0 < B ∧ ∀ (n : ℕ) (M : ComplexManifold n) (g : HermitianField M)
      (u : M.Carrier → ℝ), SmoothFn u →
      (∀ x, gradNormSq g u x ≤ C ^ 2) →
      (∀ x,
        (levi u x - ((-(C / u x) : ℝ) : ℂ) • gMat g x).PosSemidef ∧
        (((C / u x : ℝ) : ℂ) • gMat g x - levi u x).PosSemidef) →
      ∀ L, 0 < L → ∀ x, 0 < u x → u x < L →
        (levi (conformalScalar u L) x - ((-(B / L ^ 2) : ℝ) : ℂ) •
          gMat (conformalField g (conformalScalar u L)) x).PosSemidef ∧
        (((B / L ^ 2 : ℝ) : ℂ) • gMat (conformalField g (conformalScalar u L)) x -
          levi (conformalScalar u L) x).PosSemidef := by
  obtain ⟨B, hB, hb⟩ := conformalProfile_scaled_levi_coefficient C hC
  refine ⟨B, hB, ?_⟩
  intro n M g u hu hgradient hlevi L hL x huxpos huxL
  let z : ComplexVector n := chartPt x x
  have hux : inChart x u z = u x := by simp [z, inChart, chartInv, chartPt]
  have hu2 : ContDiffAt ℝ 2 (inChart x u) z :=
    (LeafProofs.L18Aux.contDiffAt_inChart hu x (mem_extChartAt_target x)).of_le (by simp)
  have hF : ContDiffAt ℝ 2 conformalProfile (inChart x u z / L) := by
    rw [hux]
    exact (conformalProfile_contDiffOn.contDiffAt
      (isOpen_Iio.mem_nhds ((div_lt_one hL).mpr huxL))).of_le (by simp)
  have hcomp : ContDiffAt ℝ 2 (fun w => conformalProfile (inChart x u w / L)) z :=
    ContDiffAt.comp (f := fun w : ComplexVector n => inChart x u w / L)
      (g := conformalProfile) z hF (hu2.div_const L)
  have hf : ContDiffAt ℝ 2 (inChart x (conformalScalar u L)) z := hcomp
  have hH : (gMat g x).PosDef :=
    LeafProofs.L12Aux.hMat_posDef g x z (mem_extChartAt_target x)
  have hα : (gMat (conformalField g (conformalScalar u L)) x).IsHermitian :=
    (LeafProofs.L12Aux.hMat_posDef _ x z (mem_extChartAt_target x)).isHermitian
  change (leviC (inChart x (conformalScalar u L)) z - _).PosSemidef ∧
    (_ - leviC (inChart x (conformalScalar u L)) z).PosSemidef
  apply leviC_sandwich_of_quadratic _ hα hf (B / L ^ 2)
  intro v
  have hquad (w : ComplexVector n) := leviC_quadratic_abs_of_sandwich
    (gMat g x) hH.isHermitian hu2 (C / u x) (hlevi x).1 (hlevi x).2 w
  have hmain := scaled_scalar_levi_quadratic_bound (gMat g x) hH hL hu2 hF
    (hgradient x) hquad v
  rw [hux] at hmain
  have hq : 0 ≤ (star (WithLp.ofLp v) ⬝ᵥ (gMat g x *ᵥ WithLp.ofLp v)).re :=
    (Complex.nonneg_iff.mp (hH.posSemidef.dotProduct_mulVec_nonneg _)).1
  have hresult := hmain.trans (mul_le_mul_of_nonneg_right (hb L (u x) hL huxpos huxL) hq)
  change |LeafProofs.L22Aux.complexLeviQuadratic
    (fun w => conformalProfile (inChart x u w / L)) z v| ≤ _ at hresult
  change |LeafProofs.L22Aux.complexLeviQuadratic
    (fun w => conformalProfile (inChart x u w / L)) z v| ≤ _
  simpa only [conformalField_gMat, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    conformalScalar, inChart, mul_assoc] using hresult

theorem conformalScalar_uniform_levi_bound (g : HermitianField M)
    (u : M.Carrier → ℝ) (hu : SmoothFn u) {C : ℝ} (hC : 0 < C)
    (hgradient : ∀ x, gradNormSq g u x ≤ C ^ 2)
    (hlevi : ∀ x,
      (levi u x - ((-(C / u x) : ℝ) : ℂ) • gMat g x).PosSemidef ∧
      (((C / u x : ℝ) : ℂ) • gMat g x - levi u x).PosSemidef) :
    ∃ B : ℝ, 0 < B ∧ ∀ L, 0 < L → ∀ x, 0 < u x → u x < L →
      (levi (conformalScalar u L) x - ((-(B / L ^ 2) : ℝ) : ℂ) •
        gMat (conformalField g (conformalScalar u L)) x).PosSemidef ∧
      (((B / L ^ 2 : ℝ) : ℂ) • gMat (conformalField g (conformalScalar u L)) x -
        levi (conformalScalar u L) x).PosSemidef := by
  obtain ⟨B, hB, hb⟩ := conformalScalar_universal_levi_bound C hC
  exact ⟨B, hB, hb n M g u hu hgradient hlevi⟩

end Yau.NodeProofs.F01Aux

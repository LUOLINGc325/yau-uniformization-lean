import Yau.Proofs.V03DualNorm

/-! Identification of the original paper Kähler pullback density and area
with the actual Hermitian norm expression, in every dimension. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

theorem realCoord_sum_realVec (r : RIdx n → ℝ) (a : RIdx n) :
    realCoord (∑ b, r b • realVec b) a = r a := by
  rcases a with ⟨i, j⟩
  fin_cases j <;>
    simp [realCoord, realVec, Fintype.sum_prod_type, Fin.sum_univ_two,
      EuclideanSpace.single, WithLp.ofLp_sum, Finset.sum_apply,
      WithLp.ofLp_smul, Pi.single_apply, apply_ite Complex.re, apply_ite Complex.im]

theorem realCoord_injective : Function.Injective (realCoord : ComplexVector n → RIdx n → ℝ) := by
  intro u v huv
  apply PiLp.ext
  intro i
  apply Complex.ext
  · simpa only [realCoord, ite_true] using congrFun huv (i, 0)
  · simpa [realCoord] using congrFun huv (i, 1)

theorem sum_realCoord_realVec (v : ComplexVector n) :
    (∑ a, realCoord v a • realVec a) = v := by
  apply realCoord_injective
  funext a
  exact realCoord_sum_realVec (realCoord v) a

theorem hermitian_chart_real_expansion (h : HermitianField M) (x : M.Carrier)
    (z u v : ComplexVector n) :
    (h (chartInv x z)).toFun (chartVec x (chartInv x z) u) (chartVec x (chartInv x z) v) =
      ∑ a, ∑ b, (realCoord u a : ℂ) * (realCoord v b : ℂ) *
        (h (chartInv x z)).toFun (chartVec x (chartInv x z) (realVec a))
          (chartVec x (chartInv x z) (realVec b)) := by
  have hstar (r : ℝ) : star (r : ℂ) = (r : ℂ) := by simp
  conv_lhs => rw [← sum_realCoord_realVec u, ← sum_realCoord_realVec v, chartVec_sum,
    chartVec_sum]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), chartVec_smul,
    hermitian_sum_left, hermitian_sum_right, HermitianInnerProduct.map_smul_left,
    HermitianInnerProduct.map_smul_right, RCLike.ofReal_eq_complex_ofReal,
    hstar, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem kahlerFormFn_eval (h : HermitianField M) (x : M.Carrier)
    (z u v : ComplexVector n) :
    (∑ a, ∑ b, kahlerFormFn h x z a b * realCoord u a * realCoord v b) =
      2 * ((h (chartInv x z)).toFun
        (chartVec x (chartInv x z) u) (chartVec x (chartInv x z) v)).im := by
  rw [hermitian_chart_real_expansion]
  simp only [Complex.im_sum, Finset.mul_sum, Complex.mul_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, kahlerFormFn]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem pullbackKahlerDensity_eq_norm (h : HermitianField M) (f : ℂ → M.Carrier) (ζ : ℂ) :
    pullbackKahlerDensity h f ζ = 2 * hermitianNormSq (h (f ζ))
      (mfderiv 𝓘(ℂ, ℂ) (ComplexModel n) f ζ
        ((tangentSpaceCastModel 𝓘(ℂ, ℂ) ζ).symm 1)) := by
  have hy : f ζ ∈ (extChartAt (ComplexModel n) (f ζ)).source := mem_extChartAt_source _
  have hround : chartInv (f ζ) (chartPt (f ζ) (f ζ)) = f ζ :=
    (extChartAt (ComplexModel n) (f ζ)).left_inv hy
  have hI : (tangentSpaceCastModel 𝓘(ℂ, ℂ) ζ).symm Complex.I =
      Complex.I • (tangentSpaceCastModel 𝓘(ℂ, ℂ) ζ).symm 1 := by
    simpa only [smul_eq_mul, mul_one] using
      (tangentSpaceCastModel 𝓘(ℂ, ℂ) ζ).symm.map_smul Complex.I (1 : ℂ)
  dsimp only [pullbackKahlerDensity]
  rw [kahlerFormFn_eval, hround, chartVec_tangentCoords _ _ hy,
    chartVec_tangentCoords _ _ hy, hI, map_smul, HermitianInnerProduct.map_smul_right]
  simp only [hermitianNormSq, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_one, mul_zero, add_zero]

theorem discArea_eq_pullback (h : HermitianField M) (f : ℂ → M.Carrier) :
    discArea h f = ∫⁻ ζ in Metric.ball (0 : ℂ) 1,
      ENNReal.ofReal (pullbackKahlerDensity h f ζ) := by
  simp_rw [pullbackKahlerDensity_eq_norm, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) by norm_num]
  rw [lintegral_const_mul' _ _ (by norm_num : (2 : ENNReal) ≠ ⊤)]
  rfl

theorem paperDiscAreaNormalization (h : HermitianField M) : PaperDiscAreaNormalization h := by
  intro _ f _
  exact ⟨fun ζ _ => pullbackKahlerDensity_eq_norm h f ζ, discArea_eq_pullback h f⟩

end Yau.Blueprint.V03Proof

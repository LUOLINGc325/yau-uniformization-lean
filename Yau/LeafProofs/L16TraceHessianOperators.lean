import Yau.LeafProofs.L16TraceSpatialGradient
import Yau.LeafProofs.L16TraceMixedHolder

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates
local instance traceHessianOperators_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance traceHessianOperators_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance traceHessianOperators_bilinearGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance traceHessianOperators_bilinearSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- Pullback of a genuine covector by a fixed spatial linear map. -/
def traceGradientPullback {n : ℕ} (P : Space n →L[ℝ] Space n) :
    (Space n →L[ℝ] ℝ) →L[ℝ] (Space n →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ (Space n) (Space n) ℝ).flip P

/-- Pullback of a genuine bilinear Hessian, bundled to preserve its Holder
    bounds by a fixed continuous linear map. -/
def traceHessianPullback {n : ℕ} (P : Space n →L[ℝ] Space n) :
    (Space n →L[ℝ] Space n →L[ℝ] ℝ) →L[ℝ] Space n →L[ℝ] Space n →L[ℝ] ℝ where
  toFun A := (traceGradientPullback P).comp (A.comp P)
  map_add' A D := by ext v w; simp [traceGradientPullback]
  map_smul' c A := by ext v w; simp [traceGradientPullback]
  cont := (continuous_id.clm_comp_const P).const_clm_comp (traceGradientPullback P)

@[simp] theorem traceGradientPullback_apply {n : ℕ} (P : Space n →L[ℝ] Space n)
    (A : Space n →L[ℝ] ℝ) : traceGradientPullback P A = A.comp P := rfl

@[simp] theorem traceHessianPullback_apply {n : ℕ} (P : Space n →L[ℝ] Space n)
    (A : Space n →L[ℝ] Space n →L[ℝ] ℝ) (v w : Space n) :
    traceHessianPullback P A v w = A (P v) (P w) := rfl

theorem traceGradientPullback_bound {n : ℕ} {P : Space n →L[ℝ] Space n}
    (hP : ‖P‖ ≤ 1) (A : Space n →L[ℝ] ℝ) : ‖traceGradientPullback P A‖ ≤ ‖A‖ := by
  exact (A.opNorm_comp_le P).trans (mul_le_of_le_one_right (norm_nonneg _) hP)

theorem traceGradientPullback_norm_le {n : ℕ} {P : Space n →L[ℝ] Space n}
    (hP : ‖P‖ ≤ 1) : ‖traceGradientPullback P‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro A
  simpa only [one_mul] using traceGradientPullback_bound hP A

theorem traceHessianPullback_bound {n : ℕ} {P : Space n →L[ℝ] Space n}
    (hP : ‖P‖ ≤ 1) (A : Space n →L[ℝ] Space n →L[ℝ] ℝ) : ‖traceHessianPullback P A‖ ≤ ‖A‖ := by
  change ‖(traceGradientPullback P).comp (A.comp P)‖ ≤ ‖A‖
  exact ((traceGradientPullback P).opNorm_comp_le _).trans
    ((mul_le_of_le_one_left (norm_nonneg _) (traceGradientPullback_norm_le hP)).trans
      ((A.opNorm_comp_le P).trans (mul_le_of_le_one_right (norm_nonneg _) hP)))

def traceNormalTensorMap {n : ℕ} (e : Space n) :
    (Space n →L[ℝ] ℝ) →L[ℝ] Space n →L[ℝ] Space n →L[ℝ] ℝ :=
  ContinuousLinearMap.smulRightL ℝ (Space n) (Space n →L[ℝ] ℝ) (innerSL ℝ e)

@[simp] theorem traceNormalTensorMap_apply {n : ℕ} (e : Space n) (A : Space n →L[ℝ] ℝ) :
    traceNormalTensorMap e A = (innerSL ℝ e).smulRight A := rfl

theorem traceNormalTensorMap_bound {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    (A : Space n →L[ℝ] ℝ) : ‖traceNormalTensorMap e A‖ = ‖A‖ := by
  rw [traceNormalTensorMap_apply,ContinuousLinearMap.norm_smulRight_apply,innerSL_apply_norm,he,one_mul]

/-- The full spatial Hessian kernel on the strict half space. Both mixed
    blocks are retained, including at nonorthogonal coefficient normalization. -/
def traceSpatialHessianKernel {n : ℕ} (e : Space n) (B : Point n → ℝ)
    (t : ℝ) (x : Space n) (r : ℝ) : Space n →L[ℝ] Space n →L[ℝ] ℝ :=
  let P := halfSpaceBoundaryProjection e
  let ξ := P x
  let a := inner ℝ e x
  let M := traceGradientPullback P
    ((2*normalGaussianKernel r a) • fderiv ℝ (heatAverage r (fun y => B (y,t-r))) ξ)
  normalHeatProfile r a • traceHessianPullback P
    (fderiv ℝ (fderiv ℝ (heatAverage r (fun y => B (y,t-r)))) ξ)+
  traceNormalTensorMap e M+(traceNormalTensorMap e M).flip-
  (normalPoissonKernel a r*heatAverage r (fun y => B (y,t-r)) ξ) •
    (innerSL ℝ e).smulRight (innerSL ℝ e)

/-- The closed half-space Hessian field uses the actual Poisson boundary
    value, rather than substituting height zero into a nonuniform age kernel. -/
def boundaryTraceHessian {n : ℕ} (e : Space n) (B : Point n → ℝ) (p : Point n) :
    Space n →L[ℝ] Space n →L[ℝ] ℝ :=
  let P := halfSpaceBoundaryProjection e
  let ξ := P p.1
  let a := inner ℝ e p.1
  let M := traceGradientPullback P (normalTraceMixed B p.2 a ξ)
  traceHessianPullback P (normalTraceTangentialSecond B p.2 a ξ)+
  traceNormalTensorMap e M+(traceNormalTensorMap e M).flip-
  tracePoissonAverage a B (ξ,p.2) • (innerSL ℝ e).smulRight (innerSL ℝ e)

/-- The actual full Hessian kernel has the cancelled tangent/mixed age
    bound plus precisely the positive Poisson normal term. -/
theorem traceSpatialHessianKernel_bound {n : ℕ} {α : ℝ} (hα : 0 ≤ α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e : Space n), ‖e‖ = 1 → ∀ (B : Point n → ℝ) (F H : ℝ),
      Continuous B → (∀ p, |B p| ≤ F) → 0 ≤ H →
      (∀ s x y, |B (x,s)-B (y,s)| ≤ H*‖x-y‖^α) →
      ∀ r : ℝ, 0 < r → ∀ t : ℝ, ∀ x : Space n, 0 ≤ inner ℝ e x →
      ‖traceSpatialHessianKernel e B t x r‖ ≤
        C*H*r^(α/2-1)+F*normalPoissonKernel (inner ℝ e x) r := by
  obtain ⟨CT,hCT,hT⟩ := heatAverage_secondFDeriv_holder_bound (n := n) hα
  obtain ⟨CM,hCM,hM⟩ := traceMixedKernel_bound (n := n) hα
  refine ⟨CT+2*CM,by positivity,?_⟩
  intro e he B F H hB hF hH0 hH r hr t x hx
  let P := halfSpaceBoundaryProjection e
  let ξ := P x
  let a := inner ℝ e x
  let A := normalHeatProfile r a • traceHessianPullback P
    (fderiv ℝ (fderiv ℝ (heatAverage r (fun y => B (y,t-r)))) ξ)
  let M := traceGradientPullback P
    ((2*normalGaussianKernel r a) • fderiv ℝ (heatAverage r (fun y => B (y,t-r))) ξ)
  let V := traceNormalTensorMap e M
  let S := (normalPoissonKernel a r*heatAverage r (fun y => B (y,t-r)) ξ) •
    (innerSL ℝ e).smulRight (innerSL ℝ e)
  have hP : ‖P‖ ≤ 1 := halfSpaceBoundaryProjection_norm_le e
  obtain ⟨hh0,hh1⟩ := normalHeatProfile_bounds hr hx
  have hA : ‖A‖ ≤ CT*H*r^(α/2-1) := by
    dsimp only [A]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hh0]
    exact ((mul_le_of_le_one_left (norm_nonneg _) hh1).trans
      (traceHessianPullback_bound hP _)).trans
      (hT r hr (fun y => B (y,t-r)) F H
        (hB.comp (continuous_id.prodMk continuous_const)) (fun y => hF (y,t-r)) hH0 (hH (t-r)) ξ)
  have hV : ‖V‖ ≤ CM*H*r^(α/2-1) := by
    rw [traceNormalTensorMap_bound he]
    exact (traceGradientPullback_bound hP _).trans (hM B F H hB hF hH0 hH r hr t a ξ)
  have hRNorm : ‖(innerSL ℝ e).smulRight (innerSL ℝ e)‖ = 1 := by
    rw [ContinuousLinearMap.norm_smulRight_apply,innerSL_apply_norm,he,one_mul]
  have hS : ‖S‖ ≤ F*normalPoissonKernel a r := by
    have hp0 := normalPoissonKernel_nonneg hx hr
    dsimp only [S]
    rw [norm_smul,hRNorm,mul_one,Real.norm_eq_abs,abs_mul,abs_of_nonneg hp0]
    have hAvg := heatAverage_bound hr (hB.comp (continuous_id.prodMk continuous_const))
      (fun y => hF (y,t-r)) ξ
    change |heatAverage r (fun y => B (y,t-r)) ξ| ≤ F at hAvg
    exact (mul_le_mul_of_nonneg_left hAvg hp0).trans_eq (mul_comm _ _)
  change ‖A+V+V.flip-S‖ ≤ _
  calc
    _ ≤ ‖A+V+V.flip‖+‖S‖ := norm_sub_le _ _
    _ ≤ (‖A+V‖+‖V.flip‖)+‖S‖ := add_le_add_left (norm_add_le _ _) _
    _ ≤ ((‖A‖+‖V‖)+‖V.flip‖)+‖S‖ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := by rw [ContinuousLinearMap.opNorm_flip]; nlinarith

/-- The full Hessian kernel is an actual Fréchet derivative of the full
    gradient kernel at every positive age. -/
theorem traceSpatialGradientKernel_hasFDerivAt {n : ℕ} {F r t : ℝ}
    (hr : 0 < r) (e : Space n) {B : Point n → ℝ}
    (hB : Continuous B) (hF : ∀ p, |B p| ≤ F) (x : Space n) :
    HasFDerivAt (fun z => traceSpatialGradientKernel e B t z r)
      (traceSpatialHessianKernel e B t x r) x := by
  let P := halfSpaceBoundaryProjection e
  let N := innerSL ℝ e
  let g : Space n → ℝ := fun y => B (y,t-r)
  have hgc : Continuous g := hB.comp (continuous_id.prodMk continuous_const)
  have hgb : ∀ y, |g y| ≤ F := fun y => hF (y,t-r)
  have hProfile := (normalHeatProfile_hasDerivAt r (inner ℝ e x)).comp_hasFDerivAt x N.hasFDerivAt
  have hAvg := ((heatAverage_hasFDerivAt_kernel_of_bounded hr hgc hgb (P x)).differentiableAt.hasFDerivAt).comp x P.hasFDerivAt
  have hGGrad := ((heatAverage_fderiv_hasFDerivAt_kernel_of_bounded hr hgc hgb (P x)).differentiableAt.hasFDerivAt).comp x P.hasFDerivAt
  have hTGrad := (traceGradientPullback P).hasFDerivAt.comp x hGGrad
  have hTangent := hProfile.smul hTGrad
  have hGNormal : HasDerivAt (fun a => 2*normalGaussianKernel r a)
      (-normalPoissonKernel (inner ℝ e x) r) (inner ℝ e x) := by
    simpa only [normalHeatProfile_deriv] using normalHeatProfile_second_hasDerivAt r (inner ℝ e x)
  have hNormal := ((hGNormal.comp_hasFDerivAt x N.hasFDerivAt).mul hAvg).smul_const N
  have h := hTangent.add hNormal
  convert h using 1 <;> try rfl
  ext v w
  simp [traceSpatialGradientKernel,traceSpatialHessianKernel,traceGradientPullback,
    traceHessianPullback,traceNormalTensorMap,P,N,g,Function.comp_def,
    ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.smulRight_apply,
    smul_smul,mul_comm,mul_left_comm,mul_assoc]
  ring

end Yau.LeafProofs.L16Aux

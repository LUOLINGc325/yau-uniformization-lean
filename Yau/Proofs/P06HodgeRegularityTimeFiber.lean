import Yau.Proofs.P06HodgeRegularitySmoothRealization
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Time derivatives are reconstructed from the actual normed model
alternating tensors. The original tangent fibres retain their topology. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

def regularityTimeModel (U : ℝ → RealForm M k) (y : M.Carrier) (t : ℝ) : HodgeJets.Fiber n k :=
  chartForm (U t) y (chartPt y y)

def regularityTimeFiberPullback (y : M.Carrier) :
    HodgeJets.Fiber n k →L[ℝ] (TangentVector M y) [⋀^Fin k]→L[ℝ] ℝ := by
  letI : ContinuousSMul ℝ (TangentVector M y) := IsScalarTower.continuousSMul ℂ
  exact ContinuousAlternatingMap.compContinuousLinearMapCLM (tangentCoordsRealContinuousLinearMap y y)

def regularityTimeDerivativeForm (U : ℝ → RealForm M k) (t : ℝ) : RealForm M k :=
  fun y => regularityTimeFiberPullback y (deriv (regularityTimeModel U y) t)

theorem regularitySmoothFormTime_slice
    (U : ℝ → RealForm M k) (hU : SmoothFormTime U (Set.Ioi 0)) {t : ℝ} (ht : 0 < t) :
    SmoothRealForm (U t) := by
  intro x I
  exact (hU x I).comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun z hz => ⟨hz,ht⟩)

theorem regularityTimeFiber_reconstruction (U : ℝ → RealForm M k) (y : M.Carrier) (t : ℝ) :
    regularityTimeFiberPullback y (regularityTimeModel U y t) = U t y := by
  apply ContinuousAlternatingMap.ext
  intro v
  change (chartForm (U t) y (chartPt y y))
    (fun r => tangentCoords y y (v r)) = U t y v
  simp only [chartForm,ContinuousAlternatingMap.compContinuousLinearMap_apply,
    chartRealContinuousLinearMap_apply,Function.comp_def]
  have hy : y ∈ (extChartAt (ComplexModel n) y).source := mem_extChartAt_source y
  have hid : chartInv y (chartPt y y) = y := (extChartAt (ComplexModel n) y).left_inv hy
  rw [hid]
  congr 1
  funext r
  exact L12Aux.chartVec_tangentCoords y y hy (v r)

theorem regularitySmoothFormTime_model
    (U : ℝ → RealForm M k) (hU : SmoothFormTime U (Set.Ioi 0)) (y : M.Carrier) :
    ContDiffOn ℝ ∞ (regularityTimeModel U y) (Set.Ioi 0) := by
  have hy : y ∈ (extChartAt (ComplexModel n) y).source := mem_extChartAt_source y
  have hz : chartPt y y ∈ chartTarget y := (extChartAt (ComplexModel n) y).map_source hy
  apply (modelForm_contDiffOn_iff _ _).mpr
  intro I
  exact (hU y I).comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun t ht => ⟨hz,ht⟩)

theorem regularityTimeDerivativeForm_hasDerivAt
    (U : ℝ → RealForm M k) (hU : SmoothFormTime U (Set.Ioi 0)) {t : ℝ} (ht : 0 < t)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) (I : Fin k → RIdx n) :
    HasDerivAt (fun s => formComponents (U s) x z I)
      (formComponents (regularityTimeDerivativeForm U t) x z I) t := by
  let y := chartInv x z
  letI : ContinuousSMul ℝ (TangentVector M y) := IsScalarTower.continuousSMul ℂ
  let C := (ContinuousAlternatingMap.apply ℝ (TangentVector M y) ℝ
    (fun r => chartVec x y (realVec (I r)))).comp (regularityTimeFiberPullback y)
  have hd := (((regularitySmoothFormTime_model U hU y).contDiffAt
    (isOpen_Ioi.mem_nhds ht)).differentiableAt (by simp)).hasDerivAt
  have hh := C.hasFDerivAt.comp_hasDerivAt t hd
  change HasDerivAt (fun s => C (regularityTimeModel U y s)) _ t at hh
  have heq : (fun s => C (regularityTimeModel U y s)) = fun s => formComponents (U s) x z I := by
    funext s
    change (regularityTimeFiberPullback y (regularityTimeModel U y s))
      (fun r => chartVec x y (realVec (I r))) = _
    rw [regularityTimeFiber_reconstruction]
    rfl
  rw [heq] at hh
  exact hh

theorem regularityTimeDerivativeForm_fiber_slope
    (U : ℝ → RealForm M k) (hU : SmoothFormTime U (Set.Ioi 0)) {t : ℝ} (ht : 0 < t)
    (y : M.Carrier) :
    Tendsto (fun s : ℝ => s⁻¹ • (U (t+s) y - U t y)) (𝓝[≠] 0)
      (𝓝 (regularityTimeDerivativeForm U t y)) := by
  have hd := (((regularitySmoothFormTime_model U hU y).contDiffAt
    (isOpen_Ioi.mem_nhds ht)).differentiableAt (by simp)).hasDerivAt
  have hh := ((regularityTimeFiberPullback y).continuous.tendsto
    (deriv (regularityTimeModel U y) t)).comp hd.tendsto_slope_zero
  simpa only [Function.comp_def,map_smul,map_sub,regularityTimeFiber_reconstruction,
    regularityTimeDerivativeForm] using hh

theorem regularityTimeDerivativeForm_smooth
    (U : ℝ → RealForm M k) (hU : SmoothFormTime U (Set.Ioi 0)) {t : ℝ} (ht : 0 < t) :
    SmoothRealForm (regularityTimeDerivativeForm U t) := by
  intro x I
  let F := fun p : ComplexVector n × ℝ => formComponents (U p.2) x p.1 I
  have hop : IsOpen (chartTarget x ×ˢ Set.Ioi (0 : ℝ)) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_Ioi
  have hDF : ContDiffOn ℝ ∞ (fun p => fderiv ℝ F p (0,1)) (chartTarget x ×ˢ Set.Ioi 0) :=
    ((hU x I).fderiv_of_isOpen hop (m := ∞) (by simp)).clm_apply contDiffOn_const
  have hslice := hDF.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun z hz => ⟨hz,ht⟩)
  apply hslice.congr
  intro z hz
  have hd := (((hU x I).contDiffAt (hop.mem_nhds
    (show (z,t) ∈ chartTarget x ×ˢ Set.Ioi 0 from ⟨hz,ht⟩))).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t z).prodMk (hasDerivAt_id t))
  exact (regularityTimeDerivativeForm_hasDerivAt U hU ht x hz I).unique hd

end Yau.NodeProofs.P06Aux

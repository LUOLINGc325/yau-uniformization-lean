import Yau.LeafProofs.L19EndpointEnergyShape
import Yau.LeafProofs.L12IndexAnalysis

/-! At the center a C1 actual normal inverse suffices to compute the
second derivative of its squared physical norm. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

/-- A squared bilinear energy has zero first derivative where its C1
argument vanishes. -/
theorem bilinearSquare_comp_fderiv_at_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : F →L[ℝ] F →L[ℝ] ℝ) (W : E → F) (z : E)
    (hW : DifferentiableAt ℝ W z) (hW0 : W z = 0) :
    fderiv ℝ (fun y => B (W y) (W y)) z = 0 := by
  have hfirst := (B.hasFDerivAt.comp z hW.hasFDerivAt).clm_apply hW.hasFDerivAt
  simp only [Function.comp_apply] at hfirst
  rw [hfirst.fderiv]
  ext u
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, hW0, map_zero, zero_apply, add_zero]

/-- The Hessian of a squared symmetric bilinear norm at a zero of a C1
map only uses the first derivative of that map. -/
theorem bilinearSquare_comp_hessian_at_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : F →L[ℝ] F →L[ℝ] ℝ) (hB : ∀ u v, B u v = B v u)
    (W : E → F) (z : E) (hW : ContDiffAt ℝ 1 W z) (hW0 : W z = 0)
    (u v : E) :
    fderiv ℝ (fderiv ℝ (fun y => B (W y) (W y))) z u v =
      2 * B (fderiv ℝ W z u) (fderiv ℝ W z v) := by
  let L : E → (F →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
    fun y => (ContinuousLinearMap.compL ℝ E F ℝ).flip (fderiv ℝ W y)
  have hL : ContinuousAt L z :=
    (ContinuousLinearMap.compL ℝ E F ℝ).flip.continuous.continuousAt.comp
      (hW.continuousAt_fderiv (by simp))
  have hm : HasFDerivAt (fun y => B (W y)) (B.comp (fderiv ℝ W z)) z :=
    B.hasFDerivAt.comp z (hW.differentiableAt (by simp)).hasFDerivAt
  have hm0 : B (W z) = 0 := by rw [hW0, map_zero]
  have hsecond := (hasFDerivAt_clm_apply_of_zero hL hm hm0).const_smul (2 : ℝ)
  have heq : fderiv ℝ (fun y => B (W y) (W y)) =ᶠ[𝓝 z]
      (fun y => (2 : ℝ) • L y (B (W y))) := by
    filter_upwards [hW.eventually (by simp)] with y hy
    have hd := hy.differentiableAt (by simp)
    have hfirst := (B.hasFDerivAt.comp y hd.hasFDerivAt).clm_apply hd.hasFDerivAt
    simp only [Function.comp_apply] at hfirst
    rw [hfirst.fderiv]
    apply ContinuousLinearMap.ext
    intro v
    change B (W y) (fderiv ℝ W y v) + B (fderiv ℝ W y v) (W y) =
      2 * B (W y) (fderiv ℝ W y v)
    rw [hB (fderiv ℝ W y v) (W y)]
    ring
  have hsecond' := heq.hasFDerivAt_iff.mpr hsecond
  rw [hsecond'.fderiv]
  rfl

/-- The genuine endpoint identity determines the derivative of a normal
inverse at the center from the already proved exponential differential. -/
theorem realNormalInverse_fderiv_at_center
    (g : SmoothMetric M) (x : M.Carrier)
    (v : ComplexVector n → ComplexVector n) (z : ComplexVector n)
    (hv : DifferentiableAt ℝ v z) (hv0 : v z = 0)
    (hends : (realExponentialCoordinates g x ∘ v) =ᶠ[𝓝 z] id) :
    fderiv ℝ v z = ContinuousLinearMap.id ℝ (ComplexVector n) := by
  have hExp : HasFDerivAt (realExponentialCoordinates g x)
      (ContinuousLinearMap.id ℝ (ComplexVector n)) (v z) := by
    rw [hv0]
    exact hasFDerivAt_realExponentialCoordinates_zero g x
  have hc := hExp.comp z hv.hasFDerivAt
  have hid := hends.hasFDerivAt_iff.mpr (hasFDerivAt_id (𝕜 := ℝ) z)
  simpa only [ContinuousLinearMap.id_comp] using hc.unique hid

/-- Actual normal-coordinate energy has Hessian twice the actual metric
at its center. Only C1 regularity of the actual inverse is required. -/
theorem realNormalInverse_energy_hessian_at_center
    (g : SmoothMetric M) (x : M.Carrier)
    (v : ComplexVector n → ComplexVector n) (z : ComplexVector n)
    (hv : ContDiffAt ℝ 1 v z) (hv0 : v z = 0)
    (hends : (realExponentialCoordinates g x ∘ v) =ᶠ[𝓝 z] id)
    (u w : ComplexVector n) :
    fderiv ℝ (fderiv ℝ (fun y => realMetricInChart g.form x
      (chartPt x x) (v y) (v y))) z u w =
        2 * realMetricInChart g.form x (chartPt x x) u w := by
  have h := bilinearSquare_comp_hessian_at_zero
    (realMetricInChart g.form x (chartPt x x))
    (realMetricInChart_symm g.form x (chartPt x x)) v z hv hv0 u w
  rw [realNormalInverse_fderiv_at_center g x v z
    (hv.differentiableAt (by simp)) hv0 hends] at h
  exact h

/-- The squared physical normal coordinate radius is C2 on a genuine C1
normal inverse branch, by the neighborhood endpoint first variation. -/
theorem realNormalInverse_energy_contDiffAt_two
    (g : SmoothMetric M) (x : M.Carrier)
    (v : ComplexVector n → ComplexVector n)
    (O : Set (ComplexVector n)) (hO : IsOpen O) (z : ComplexVector n)
    (hz : z ∈ O) (hx : z ∈ chartTarget x)
    (hv : ContDiffOn ℝ 1 v O)
    (hends : ∀ y ∈ O, realNormalExponentialMap g x (v y) = chartInv x y) :
    ContDiffAt ℝ 2 (fun y => realMetricInChart g.form x (chartPt x x) (v y) (v y)) z := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  let Q := fun y => (⟨x, realFrameCLM x x (v y)⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
  have hW : ContMDiffOn 𝓘(ℝ, ComplexVector n)
      𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) x) 1
      (fun y => realFrameCLM x x (v y)) O :=
    (realFrameCLM x x).contMDiff.comp_contMDiffOn hv.contMDiffOn
  have hQ : ContMDiffOn 𝓘(ℝ, ComplexVector n) (realPhaseModel n) 1 Q O :=
    ((realTangentFiber_contMDiff g x).of_le (by simp)).comp_contMDiffOn hW
  have hQends : ∀ y ∈ O, (Q y).proj = x ∧
      (realGeodesicFlow g (Q y) 1).proj = chartInv x y := by
    intro y hy
    exact ⟨rfl, hends y hy⟩
  have hE0 : ContDiffAt ℝ 2 (realSegmentEnergy g 1 ∘ Q) z :=
    realSegmentEnergy_endpoint_contDiffAt_two g 1 x x Q O hO z hz hx hQ hQends
  have hE : ContDiffAt ℝ 2 (fun y => 2 * realSegmentEnergy g 1 (Q y)) z :=
    contDiffAt_const.mul hE0
  convert hE using 1
  funext y
  rw [realMetricInChart_self_frame]
  dsimp only [realSegmentEnergy, Q, realTangentEnergy]
  ring

/-- The same actual normal energy dominates the original length-distance
square, whether or not the neighboring segment is minimizing. -/
theorem inducedDistance_sq_le_realNormalEnergy
    (g : SmoothMetric M) (x : M.Carrier) (w : ComplexVector n) :
    inducedDistance g.form x (realNormalExponentialMap g x w) ^ 2 ≤
      realMetricInChart g.form x (chartPt x x) w w := by
  letI := inducedMetricSpace g
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  have hd := inducedDistance_realExponentialMap_le g x (realFrameCLM x x w)
  have hn : 0 ≤ inducedDistance g.form x (realNormalExponentialMap g x w) :=
    g.induced_distance_nonneg _ _
  have hs := (sq_le_sq₀ hn (norm_nonneg (realFrameCLM x x w))).mpr hd
  rw [realMetricInChart_self_frame]
  change _ ≤ ⟪realFrameCLM x x w, realFrameCLM x x w⟫_ℝ
  rw [real_inner_self_eq_norm_sq]
  exact hs

end Yau.LeafProofs.L19Aux

import Yau.Proofs.P06CylinderRegularityProlongationHeat
import Yau.Proofs.P06HodgeRegularityCoefficients

/-! The original form heat equation gives the computed scalar-principal
finite system, with the original clock -1/2, on every actual chart. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau Yau.Blueprint Yau.Parabolic Yau.LeafProofs.L03

theorem smoothFormTime_slice {n k : ℕ} {M : ComplexManifold n}
    {U : ℝ → RealForm M k} (hU : SmoothFormTime U (Set.Ioi 0)) {t : ℝ} (ht : 0 < t) :
    SmoothRealForm (U t) := by
  intro x I
  exact (hU x I).comp (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz,ht⟩)

theorem hodgeCoordinate_hasDerivAt {n k : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {U : ℝ → RealForm M k} (hU : SmoothFormTime U (Set.Ioi 0))
    (hPDE : FormHeatEquation g.form U) (x : M.Carrier) {α : Type} [Fintype α]
    (b : Basis α ℝ (HodgeJets.Fiber n k)) {z : ComplexVector n} (hz : z ∈ chartTarget x)
    {t : ℝ} (ht : 0 < t) (r : α) :
    HasDerivAt (fun s => hodgeRegularityCoord b (U s) x z r)
      (-(hodgeRegularityCoord b (hodgeRealForm g.form k (U t)) x z r)/2) t := by
  let H := hodgeRealForm g.form k (U t)
  have hComp (I : Fin k → RIdx n) : HasDerivAt
      (fun s => modelFormCoefficientMap n k (chartForm (U s) x z) I)
      (-(modelFormCoefficientMap n k (chartForm H x z) I)/2) t := by
    have h := hPDE x z hz t ht I
    have hRep := hodgeRealForm_represents g μ hμ (U t) (smoothFormTime_slice hU ht) x z hz I
    change HasDerivAt (fun s => formComponents (U s) x z I)
      (-(formComponents H x z I)/2) t
    change HasDerivAt (fun s => formComponents (U s) x z I)
      (-(hodgeComponents g.form x k (formComponents (U t) x) z I)/2) t at h
    change formComponents H x z I = hodgeComponents g.form x k (formComponents (U t) x) z I at hRep
    rw [← hRep] at h
    exact h
  have hArray : HasDerivAt (fun s => modelFormCoefficientMap n k (chartForm (U s) x z))
      (fun I => -(modelFormCoefficientMap n k (chartForm H x z) I)/2) t :=
    hasDerivAt_pi.mpr hComp
  let L := (b.coord r).toContinuousLinearMap.comp (modelFormReconstruction n k)
  have h := L.hasFDerivAt.comp_hasDerivAt t hArray
  have hTarget : (fun I => -(modelFormCoefficientMap n k (chartForm H x z) I)/2) =
      (-(1/2 : ℝ)) • modelFormCoefficientMap n k (chartForm H x z) := by
    funext I
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hTarget, map_smul] at h
  simp only [L, Function.comp_apply, ContinuousLinearMap.comp_apply,
    modelFormReconstruction_coefficient, smul_eq_mul] at h
  convert h using 1
  · funext s
    change hodgeRegularityCoord b (U s) x z r =
      (b.coord r).toContinuousLinearMap (modelFormReconstruction n k
        (modelFormCoefficientMap n k (chartForm (U s) x z)))
    rw [modelFormReconstruction_coefficient]
    rfl
  · change -(b.repr (chartForm H x z) r)/2 = (-(1/2 : ℝ)) * b.repr (chartForm H x z) r
    ring

section Slices
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem joint_space_direction {f : E × ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (z : E) (t : ℝ) (v : E) :
    regularityDirection (v,0) f (z,t) = regularityDirection v (fun y => f (y,t)) z := by
  have hIncl : HasFDerivAt (fun y : E => (y,t))
      ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ)) z :=
    (hasFDerivAt_id z).prodMk (hasFDerivAt_const t z)
  have h := ((hf.differentiable (by simp) (z,t)).hasFDerivAt.comp z hIncl).fderiv
  have hv := congrArg (fun L : E →L[ℝ] ℝ => L v) h
  exact hv.symm

theorem joint_space_second {f : E × ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (z : E) (t : ℝ) (v w : E) :
    regularityDirection (v,0) (regularityDirection (w,0) f) (z,t) =
      regularityDirection v (regularityDirection w (fun y => f (y,t))) z := by
  rw [joint_space_direction (regularityDirection_contDiff hf (w,0))]
  have hFun : (fun y => regularityDirection (w,0) f (y,t)) =
      regularityDirection w (fun y => f (y,t)) := funext (fun y => joint_space_direction hf y t w)
  rw [hFun]

end Slices

theorem actual_hodge_heatEquation {n k : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (U : ℝ → RealForm M k) (hU : SmoothFormTime U (Set.Ioi 0)) (hPDE : FormHeatEquation g.form U)
    (x : M.Carrier) {α : Type} [Fintype α] [DecidableEq α]
    (b : Basis α ℝ (HodgeJets.Fiber n k))
    (q : RIdx n → RIdx n → Point n → ℝ)
    (e1 : α → α → RIdx n → Point n → ℝ) (e0 : α → α → Point n → ℝ)
    (W : Point n → α → ℝ) (hW : ∀ r, ContDiff ℝ ∞ (fun p => W p r))
    {Q : Set (Point n)} (hQ : Q ⊆ chartTarget x ×ˢ Set.Ioi 0)
    (hGerm : ∀ p ∈ Q, ∀ r, (fun s => W s r) =ᶠ[𝓝 p]
      (fun s => hodgeRegularityCoord b (U s.2) x s.1 r))
    (hq : ∀ p ∈ Q, ∀ i j, q i j p = hodgeRegularityQ g.form x i j p.1)
    (he1 : ∀ p ∈ Q, ∀ r c i, e1 r c i p = hodgeRegularityE1 g.form x b r c i p.1)
    (he0 : ∀ p ∈ Q, ∀ r c, e0 r c p = hodgeRegularityE0 g.form x b r c p.1) :
    heatEquation q e1 e0 Q W := by
  intro p hp r
  rcases p with ⟨z,t⟩
  have hz := (hQ hp).1
  have ht := (hQ hp).2
  have hSlice (c : α) : (fun y => W (y,t) c) =ᶠ[𝓝 z]
      (fun y => hodgeRegularityCoord b (U t) x y c) :=
    (hGerm (z,t) hp c).comp_tendsto (continuous_id.prodMk continuous_const).continuousAt.tendsto
  have hFirst (c : α) (i : RIdx n) :
      regularityDirection (realVec i) (fun y => W (y,t) c) z =
      regularityDirection (realVec i) (fun y => hodgeRegularityCoord b (U t) x y c) z := by
    exact congrArg (fun L : ComplexVector n →L[ℝ] ℝ => L (realVec i)) (hSlice c).fderiv.eq_of_nhds
  have hSecond (i j : RIdx n) :
      regularityDirection (realVec i) (regularityDirection (realVec j) (fun y => W (y,t) r)) z =
      regularityDirection (realVec i) (regularityDirection (realVec j)
        (fun y => hodgeRegularityCoord b (U t) x y r)) z := by
    have hD : regularityDirection (realVec j) (fun y => W (y,t) r) =ᶠ[𝓝 z]
        regularityDirection (realVec j) (fun y => hodgeRegularityCoord b (U t) x y r) :=
      (hSlice r).fderiv.mono fun y hy => congrArg (fun L : ComplexVector n →L[ℝ] ℝ => L (realVec j)) hy
    exact congrArg (fun L : ComplexVector n →L[ℝ] ℝ => L (realVec i)) hD.fderiv.eq_of_nhds
  have hOp : systemOperator (fun i => (realVec i,0)) q e1 e0 W (z,t) r =
      hodgeRegularityCoord b (hodgeRealForm g.form k (U t)) x z r := by
    rw [hodgeRegularity_chart_system g μ hμ (U t) (smoothFormTime_slice hU ht) x b hz r]
    simp only [systemOperator, hq (z,t) hp, he1 (z,t) hp, he0 (z,t) hp,
      joint_space_direction (hW _), joint_space_second (hW _), hFirst, hSecond,
      hodgeRegularityQ, realModelBasis_apply]
    have hValue (c : α) : W (z,t) c = hodgeRegularityCoord b (U t) x z c :=
      (hGerm (z,t) hp c).eq_of_nhds
    simp only [hValue]
  have hTimeGerm : (fun s => W (z,s) r) =ᶠ[𝓝 t]
      (fun s => hodgeRegularityCoord b (U s) x z r) :=
    (hGerm (z,t) hp r).comp_tendsto (continuous_const.prodMk continuous_id).continuousAt.tendsto
  have hTime := (hodgeCoordinate_hasDerivAt g μ hμ hU hPDE x b hz ht r).congr_of_eventuallyEq hTimeGerm
  have hComputed : HasDerivAt (fun s => W (z,s) r)
      (fderiv ℝ (fun p => W p r) (z,t) (0,1)) t :=
    ((hW r).differentiable (by simp) (z,t)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t z).prodMk (hasDerivAt_id t))
  rw [hOp]
  exact hComputed.unique hTime

end Yau.NodeProofs.P06Aux.CylinderReg

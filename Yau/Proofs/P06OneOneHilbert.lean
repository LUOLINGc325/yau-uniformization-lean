import Yau.Proofs.P06WeitzenbockProjectionEnergy
import Yau.Proofs.P06HodgeEnergyLowerSemicontinuity

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

theorem jPullback_coefficients (A : RealForm M 2) (c y : M.Carrier)
    (I : Fin 2 → RIdx n) :
    P06Weitzenbock.jPullbackRealForm A y (fun r => chartVec c y (realVec (I r))) =
      (∏ r, L12Aux.jSign (I r)) * A y
        (fun r => chartVec c y (realVec (L12Aux.jIndex n (I r)))) := by
  rw [P06Weitzenbock.jPullbackRealForm_apply]
  have hv : (fun r => Complex.I • chartVec c y (realVec (I r))) =
      fun r => L12Aux.jSign (I r) • chartVec c y (realVec (L12Aux.jIndex n (I r))) := by
    funext r
    rw [← L12Aux.chartVec_complex_smul, G04Aux.I_smul_realVec, G04Aux.chartVec_real_smul]
  rw [hv, ContinuousAlternatingMap.map_smul_univ]
  rfl

theorem l2RealForm_jPullback (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M 2) (hA : L2RealForm g.form μ A) :
    L2RealForm g.form μ (P06Weitzenbock.jPullbackRealForm A) := by
  constructor
  · intro c I
    have hm := (hA.1 c (fun r => L12Aux.jIndex n (I r))).const_mul (∏ r, L12Aux.jSign (I r))
    exact hm.congr (Filter.Eventually.of_forall fun y => (jPullback_coefficients A c y I).symm)
  · have he : formNormSq g.form (P06Weitzenbock.jPullbackRealForm A) = formNormSq g.form A :=
      funext (fun x => P06Weitzenbock.formInner_jPullback g.form A A x)
    rw [he]
    exact hA.2

theorem l2RealForm_oneOneProjection (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M 2) (hA : L2RealForm g.form μ A) :
    L2RealForm g.form μ (P06Weitzenbock.oneOneProjection A) :=
  l2RealForm_smul g μ (1 / 2) _ (l2RealForm_add g μ A _ hA (l2RealForm_jPullback g μ A hA))

def oneOneProjectionLinear : RealForm M 2 →ₗ[ℝ] RealForm M 2 where
  toFun := P06Weitzenbock.oneOneProjection
  map_add' A B := by
    simp only [P06Weitzenbock.oneOneProjection, P06Weitzenbock.jPullbackRealForm_add, smul_add]
    abel
  map_smul' c A := by
    change P06Weitzenbock.oneOneProjection (c • A) = c • P06Weitzenbock.oneOneProjection A
    simp only [P06Weitzenbock.oneOneProjection, P06Weitzenbock.jPullbackRealForm_smul,
      smul_add, smul_smul, mul_comm]

def oneOneProjectionL2Linear (g : SmoothMetric M) (μ : Measure M.Carrier) :
    L2FormSpace g μ 2 →ₗ[ℝ] L2FormSpace g μ 2 where
  toFun u := L2FormSpace.ofSection (P06Weitzenbock.oneOneProjection u.toSection)
    (l2RealForm_oneOneProjection g μ u.toSection u.toSection_l2)
  map_add' u v := by
    apply L2FormSpace.toSection_injective g μ 2
    change oneOneProjectionLinear (u + v).toSection =
      oneOneProjectionLinear u.toSection + oneOneProjectionLinear v.toSection
    rw [L2FormSpace.toSection_add, map_add]
  map_smul' c u := by
    apply L2FormSpace.toSection_injective g μ 2
    change oneOneProjectionLinear (c • u).toSection = c • oneOneProjectionLinear u.toSection
    rw [L2FormSpace.toSection_smul, map_smul]

theorem oneOneProjectionL2Linear_toSection (g : SmoothMetric M) (μ : Measure M.Carrier)
    (u : L2FormSpace g μ 2) :
    (oneOneProjectionL2Linear g μ u).toSection = P06Weitzenbock.oneOneProjection u.toSection := rfl

theorem oneOneProjectionL2Linear_norm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (u : L2FormSpace g μ 2) : ‖oneOneProjectionL2Linear g μ u‖ ≤ ‖u‖ := by
  have hi := integral_mono
    (formNormSq_integrable g μ _ (l2RealForm_oneOneProjection g μ u.toSection u.toSection_l2))
    (formNormSq_integrable g μ u.toSection u.toSection_l2)
    (fun x => P06Weitzenbock.projection_normSq_le g.form u.toSection x)
  have hs : ‖oneOneProjectionL2Linear g μ u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    simpa only [l2FormSpace_norm_sq, oneOneProjectionL2Linear_toSection] using hi
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

def oneOneProjectionHilbert (g : SmoothMetric M) (μ : Measure M.Carrier) :
    L2FormHilbert g μ 2 →L[ℝ] L2FormHilbert g μ 2 :=
  ((oneOneProjectionL2Linear g μ).mkContinuous 1
    (fun u => by simpa only [one_mul] using oneOneProjectionL2Linear_norm_le g μ u)).completion

theorem oneOneProjectionHilbert_realize (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M 2) (hA : L2RealForm g.form μ A) :
    oneOneProjectionHilbert g μ (realizeActualForm g μ A hA) =
      realizeActualForm g μ (P06Weitzenbock.oneOneProjection A) (l2RealForm_oneOneProjection g μ A hA) :=
  ContinuousLinearMap.completion_apply_coe _ (L2FormSpace.ofSection A hA)

theorem oneOneProjectionHilbert_norm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (f : L2FormHilbert g μ 2) : ‖oneOneProjectionHilbert g μ f‖ ≤ ‖f‖ := by
  refine UniformSpace.Completion.induction_on f ?_ ?_
  · exact isClosed_le ((oneOneProjectionHilbert g μ).continuous.norm) continuous_norm
  · intro u
    change ‖oneOneProjectionHilbert g μ (realizeActualForm g μ u.toSection u.toSection_l2)‖ ≤
      ‖realizeL2Form g μ u‖
    rw [oneOneProjectionHilbert_realize]
    change ‖realizeL2Form g μ (oneOneProjectionL2Linear g μ u)‖ ≤ ‖realizeL2Form g μ u‖
    simpa only [realizeL2Form, UniformSpace.Completion.norm_coe] using
      oneOneProjectionL2Linear_norm_le g μ u

theorem oneOneProjectionHilbert_idempotent (g : SmoothMetric M) (μ : Measure M.Carrier)
    (f : L2FormHilbert g μ 2) :
    oneOneProjectionHilbert g μ (oneOneProjectionHilbert g μ f) = oneOneProjectionHilbert g μ f := by
  refine UniformSpace.Completion.induction_on f ?_ ?_
  · exact isClosed_eq ((oneOneProjectionHilbert g μ).continuous.comp (oneOneProjectionHilbert g μ).continuous)
      (oneOneProjectionHilbert g μ).continuous
  · intro u
    change oneOneProjectionHilbert g μ (oneOneProjectionHilbert g μ (realizeActualForm g μ u.toSection u.toSection_l2)) =
      oneOneProjectionHilbert g μ (realizeActualForm g μ u.toSection u.toSection_l2)
    simp only [oneOneProjectionHilbert_realize]
    apply realizeActualForm_congr
    exact P06Weitzenbock.oneOneProjection_idempotent u.toSection

theorem oneOneProjectionHilbert_selfadjoint (g : SmoothMetric M) (μ : Measure M.Carrier)
    (f k : L2FormHilbert g μ 2) :
    inner ℝ (oneOneProjectionHilbert g μ f) k = inner ℝ f (oneOneProjectionHilbert g μ k) := by
  refine UniformSpace.Completion.induction_on₂ f k ?_ ?_
  · exact isClosed_eq
      ((oneOneProjectionHilbert g μ).continuous.comp continuous_fst |>.inner continuous_snd)
      (continuous_fst.inner ((oneOneProjectionHilbert g μ).continuous.comp continuous_snd))
  · intro u v
    change inner ℝ (oneOneProjectionHilbert g μ (realizeActualForm g μ u.toSection u.toSection_l2))
      (realizeActualForm g μ v.toSection v.toSection_l2) =
      inner ℝ (realizeActualForm g μ u.toSection u.toSection_l2)
        (oneOneProjectionHilbert g μ (realizeActualForm g μ v.toSection v.toSection_l2))
    rw [oneOneProjectionHilbert_realize, oneOneProjectionHilbert_realize,
      realizeActualForm_inner, realizeActualForm_inner]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
      P06Weitzenbock.formInner_oneOneProjection_selfadjoint g.form u.toSection v.toSection x)

end Yau.NodeProofs.P06Aux

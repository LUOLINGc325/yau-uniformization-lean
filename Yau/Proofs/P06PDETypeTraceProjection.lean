import Yau.Proofs.P06PDETypeTraceInitial
import Yau.Proofs.P06WeitzenbockCoreMaps
import Yau.Proofs.P06FormUniqueness

/-! The actual type projection of any solution stays in the original PDE class. -/
noncomputable section
open Filter MeasureTheory
open scoped Manifold Topology ContDiff
namespace Yau.NodeProofs.P06Aux.PDETypeTrace
open Yau Yau.Blueprint Yau.LeafProofs G04Aux L23Aux L12Aux P06Weitzenbock
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

 theorem oneOneProjection_components (A : RealForm M 2) (x : M.Carrier)
    (z : ComplexVector n) (I : Fin 2 → RIdx n) :
    formComponents (oneOneProjection A) x z I = (1 / 2 : ℝ) *
      (formComponents A x z I + (∏ r, jSign (I r)) *
        formComponents A x z (fun r => jIndex n (I r))) := by
  simp only [oneOneProjection, L03.formComponents_smul, L03.formComponents_add,
    Pi.smul_apply, Pi.add_apply, smul_eq_mul, jPullbackRealForm_components]

theorem projection_smoothTime {S : Set ℝ} {U : ℝ → RealForm M 2}
    (hU : SmoothFormTime U S) : SmoothFormTime (fun t => oneOneProjection (U t)) S := by
  intro x I
  apply (contDiffOn_const.mul ((hU x I).add
    (contDiffOn_const.mul (hU x (fun r => jIndex n (I r)))))).congr
  intro p hp
  exact oneOneProjection_components _ _ _ _

theorem projection_initial {A : RealForm M 2} {U : ℝ → RealForm M 2}
    (hA : SmoothRealForm A) (hU : SmoothFormTime U (Set.Ioi 0))
    (h0 : FormSmoothInitial U A) :
    FormSmoothInitial (fun t => oneOneProjection (U t)) (oneOneProjection A) := by
  rw [formSmoothInitial_iff_smallJets] at h0 ⊢
  refine ⟨by rw [h0.1], ?_⟩
  intro x I
  have hO : IsOpen (chartTarget x) := isOpen_extChartAt_target (I := ComplexModel n) x
  have hsm (J : Fin 2 → RIdx n) (t : ℝ) (ht : 0 < t) :
      ContDiffOn ℝ ∞ (fun z => formComponents (U t) x z J - formComponents A x z J)
        (chartTarget x) := (smoothFormTime_slice hU ht x J).sub (hA x J)
  have hh := smallJetsOn_const_mul hO
    (fun t ht => (hsm I t ht).add (contDiffOn_const.mul (hsm (fun r => jIndex n (I r)) t ht)))
    (smallJetsOn_add hO (hsm I)
      (fun t ht => contDiffOn_const.mul (hsm (fun r => jIndex n (I r)) t ht))
      (h0.2 x I) (smallJetsOn_const_mul hO (hsm _) (h0.2 x _) (∏ r, jSign (I r)))) (1 / 2)
  convert hh using 1 <;> try rfl
  funext t z
  rw [oneOneProjection_components, oneOneProjection_components]
  ring

theorem projection_generator (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (A : RealForm M 2) (hA : SmoothRealForm A) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (I : Fin 2 → RIdx n) :
    hodgeGeneratorComponents g.form x (formComponents (oneOneProjection A) x) z I =
      (1 / 2 : ℝ) * (hodgeGeneratorComponents g.form x (formComponents A x) z I +
        (∏ r, jSign (I r)) *
          hodgeGeneratorComponents g.form x (formComponents A x) z (fun r => jIndex n (I r))) := by
  have hp := congrArg (fun F : RealForm M 2 => formComponents F x z I)
    (hodge_oneOneProjection g μ hμ hk A hA)
  rw [hodge_represents g.form (L12Aux.metricSmooth_of_smoothMetric g) _
      (oneOneProjection_smooth A hA) x z hz I,
    oneOneProjection_components] at hp
  rw [hodge_represents g.form (L12Aux.metricSmooth_of_smoothMetric g) A hA x z hz I,
    hodge_represents g.form (L12Aux.metricSmooth_of_smoothMetric g) A hA x z hz
      (fun r => jIndex n (I r))] at hp
  unfold hodgeGeneratorComponents
  rw [hp]
  ring

theorem projection_heatEquation (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    {U : ℝ → RealForm M 2} (hU : SmoothFormTime U (Set.Ioi 0))
    (hPDE : FormHeatEquation g.form U) :
    FormHeatEquation g.form (fun t => oneOneProjection (U t)) := by
  intro x z hz t ht I
  have hd := ((hPDE x z hz t ht I).add
    ((hPDE x z hz t ht (fun r => jIndex n (I r))).const_mul
      (∏ r, jSign (I r)))).const_mul (1 / 2 : ℝ)
  rw [← projection_generator g μ hμ hk (U t) (smoothFormTime_slice hU ht) x hz I] at hd
  convert hd using 1
  funext s
  exact oneOneProjection_components _ _ _ _

theorem projection_boundedFormHeat (X : KahlerManifold n)
    {A : RealForm X.manifold 2} {U : ℝ → RealForm X.manifold 2}
    (hA : SmoothRealForm A) (hU : IsBoundedFormHeat X.metric.form A U) :
    IsBoundedFormHeat X.metric.form (oneOneProjection A) (fun t => oneOneProjection (U t)) := by
  obtain ⟨μ, hμ⟩ := Yau.Proofs.G02Aux.exists_riemannianVolume X.metric.form
    (L12Aux.metricSmooth_of_smoothMetric X.metric)
  refine ⟨projection_smoothTime hU.1, projection_initial hA hU.1 hU.2.1, ?_,
    projection_heatEquation X.metric μ hμ X.kahler_metric hU.1 hU.2.2.2⟩
  intro T hT
  obtain ⟨B, hB, hb⟩ := hU.2.2.1 T hT
  exact ⟨B, hB, fun x t ht htT => (projection_normSq_le _ _ _).trans (hb x t ht htT)⟩

/-- The type clause of the original HodgeTypeAndOrder target. -/
theorem boundedFormHeat_oneOne (X : KahlerManifold n)
    (A : RealForm X.manifold 2) (U : ℝ → RealForm X.manifold 2)
    (hA : BoundedOneOneData X.metric.form A) (hU : IsBoundedFormHeat X.metric.form A U)
    (t : ℝ) (ht : 0 < t) : RealOneOne (U t) := by
  have hp := projection_boundedFormHeat X hA.1 hU
  rw [oneOneProjection_fixed A hA.2.1] at hp
  have he := boundedFormHeat_unique X A U (fun t => oneOneProjection (U t)) hU hp t ht.le
  rw [he]
  exact oneOneProjection_type _

end Yau.NodeProofs.P06Aux.PDETypeTrace

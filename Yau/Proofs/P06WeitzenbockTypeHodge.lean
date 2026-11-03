import Yau.Proofs.P06WeitzenbockTypeCurvature

noncomputable section
open MeasureTheory
open scoped Matrix Manifold Topology ContDiff
namespace Yau.NodeProofs.P06Weitzenbock
open Yau Yau.LeafProofs G04Aux L23Aux L12Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

def hodgeTwoMatrix (h : HermitianField M) (A : RealForm M 2) (c : M.Carrier)
    (z : ComplexVector n) : Matrix (RIdx n) (RIdx n) ℝ :=
  fun d e => hodgeComponents h c 2 (formComponents A c) z ![d,e]

theorem hodgeTwoMatrix_formula (h : HermitianField M) (hs : MetricSmooth h)
    (A : RealForm M 2) (hA : SmoothRealForm A) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    hodgeTwoMatrix h A c z = roughTwoMatrix h A c z + curvatureTwoMatrix h A c z := by
  ext d e
  exact hodgeTwo_eq_rough_add_curvature h hs A hA c hz ![d,e]

theorem hodgeTwoMatrix_jPullback (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (A : RealForm M 2) (hA : SmoothRealForm A)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    hodgeTwoMatrix h (jPullbackRealForm A) c z =
      (jMatrix n)ᵀ * hodgeTwoMatrix h A c z * jMatrix n := by
  rw [hodgeTwoMatrix_formula h hs _ (jPullbackRealForm_smooth A hA) c hz,
    hodgeTwoMatrix_formula h hs A hA c hz,
    roughTwoMatrix_jPullback h hs hk A hA c hz, curvatureTwoMatrix_jPullback h hs hk A c hz]
  noncomm_ring

theorem chartFormMatrix_hodge (h : HermitianField M) (hs : MetricSmooth h)
    (A : RealForm M 2) (hA : SmoothRealForm A) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    chartFormMatrix (L03.hodgeRealForm h 2 A) c z = hodgeTwoMatrix h A c z := by
  ext d e
  exact hodge_represents h hs A hA c z hz ![d,e]

/-- The original Hodge expression commutes with J on both form slots,
without any closedness or type assumption on the input. -/
theorem hodge_jPullback (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (A : RealForm M 2) (hA : SmoothRealForm A) :
    L03.hodgeRealForm h 2 (jPullbackRealForm A) = jPullbackRealForm (L03.hodgeRealForm h 2 A) := by
  apply L03.realForm_eq_of_center_components
  intro x I
  have hx : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have he : chartFormMatrix (L03.hodgeRealForm h 2 (jPullbackRealForm A)) x (chartPt x x) =
      chartFormMatrix (jPullbackRealForm (L03.hodgeRealForm h 2 A)) x (chartPt x x) := by
    calc
      _ = hodgeTwoMatrix h (jPullbackRealForm A) x (chartPt x x) :=
        chartFormMatrix_hodge h hs _ (jPullbackRealForm_smooth A hA) x hx
      _ = (jMatrix n)ᵀ * hodgeTwoMatrix h A x (chartPt x x) * jMatrix n :=
        hodgeTwoMatrix_jPullback h hs hk A hA x hx
      _ = (jMatrix n)ᵀ * chartFormMatrix (L03.hodgeRealForm h 2 A) x (chartPt x x) * jMatrix n := by
        rw [chartFormMatrix_hodge h hs A hA x hx]
      _ = _ := (chartFormMatrix_jPullback _ x (chartPt x x)).symm
  rw [formComponents_degree_two, formComponents_degree_two]
  exact congrArg (fun K : Matrix (RIdx n) (RIdx n) ℝ => K (I 0) (I 1)) he

theorem hodge_oneOneProjection (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (A : RealForm M 2) (hA : SmoothRealForm A) :
    L03.hodgeRealForm g.form 2 (oneOneProjection A) =
      oneOneProjection (L03.hodgeRealForm g.form 2 A) := by
  rw [oneOneProjection, L03.hodgeRealForm_smul g μ hμ,
    L03.hodgeRealForm_add g μ hμ A (jPullbackRealForm A) hA (jPullbackRealForm_smooth A hA),
    hodge_jPullback g.form (L12Aux.metricSmooth_of_smoothMetric g) hk A hA]
  · rfl
  · exact L03.smoothRealForm_add _ _ hA (jPullbackRealForm_smooth A hA)

end Yau.NodeProofs.P06Weitzenbock

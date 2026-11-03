import Yau.Proofs.C01PositiveTimeBisectional
import Yau.Proofs.C01GriffithsRicci
import Yau.Proofs.C01RicciTimeBoundary
import Yau.Proofs.G01BisectionalNumerator

/-! The original paper curvature hypothesis supplies strict initial
Chern bisectional and Ricci positivity.  Positive-time joint positivity
then gives the entire original nonnegative bisectional clause. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_metricSmooth_nonneg
    (hflow : LocalizedFlow X o h U P ρ) (t : ℝ) (ht : 0 ≤ t) : MetricSmooth (h t) := by
  intro x a b
  exact (hflow.1.2.1 x a b).comp (contDiffOn_id.prodMk contDiffOn_const)
    (fun z hz => ⟨hz, ht⟩)

theorem localizedFlow_hMat_fixedTime_contDiffOn
    (hflow : LocalizedFlow X o h U P ρ) (t : ℝ) (ht : 0 ≤ t) (x : Pt X) (a b : Fin n) :
    ContDiffOn ℝ ∞ (fun z => hMat (h t) x z a b) (chartTarget x) :=
  (Alignment.Y03Proof.metricFamily_hMat_contDiffOn hflow.1.2.1 x a b).comp
    (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz, ht⟩)

theorem localizedFlow_initial_griffithsPositive
    (hflow : LocalizedFlow X o h U P ρ) : GriffithsPositive X.metric.form := by
  have hs : MetricSmooth X.metric.form := by
    rw [← hflow.1.1]
    exact localizedFlow_metricSmooth_nonneg hflow 0 le_rfl
  intro x ξ η hξ hη
  have hcoord (v : ComplexVector n) : tangentCoordinates x (chartVec x x v) = v :=
    Yau.LeafProofs.L12Aux.tangentCoords_chartVec x x (mem_extChartAt_source x) v
  have hne (v : ComplexVector n) (hv : v ≠ 0) : chartVec x x v ≠ 0 := by
    intro hz
    apply hv
    have hc := congrArg (tangentCoordinates x) hz
    rw [hcoord] at hc
    simpa only [tangentCoordinates, map_zero] using! hc
  have hp := X.positive_bisectional_curvature x (chartVec x x ξ) (chartVec x x η)
    (hne ξ hξ) (hne η hη)
  change 0 < paperBisectionalNumerator X.metric.form x (chartVec x x ξ) (chartVec x x η) at hp
  rw [Yau.NodeProofs.G01Aux.paper_numerator_eq_bisectionalForm X.metric.form hs X.kahler_metric,
    hcoord, hcoord] at hp
  linarith

theorem localizedFlow_nonnegBisectional
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (t : ℝ) (ht : 0 ≤ t) : NonnegBisectional (h t) := by
  by_cases ht0 : t = 0
  · subst t
    rw [hflow.1.1]
    intro x ξ η
    by_cases hξ : ξ = 0
    · subst ξ
      simp [bisectionalForm]
    by_cases hη : η = 0
    · subst η
      simp [bisectionalForm]
    exact (localizedFlow_initial_griffithsPositive hflow x ξ η hξ hη).le
  · exact localizedFlow_nonnegBisectional_positive hflow hjoint t (lt_of_le_of_ne ht (Ne.symm ht0))

theorem localizedFlow_initial_ricci_posDef
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X) : (ricci (h 0) x).PosDef := by
  have hherm := localizedFlow_ricci_isHermitian_nonneg hflow x (t := 0) le_rfl
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hherm
  intro v hv
  let η : ComplexVector n := WithLp.toLp 2 v
  have hη : η ≠ 0 := by
    intro hz
    apply hv
    exact congrArg WithLp.ofLp hz
  have hg (y : Pt X) (a b : Fin n) :
      ContDiffOn ℝ ∞ (fun z => hMat X.metric.form y z a b) (chartTarget y) := by
    rw [← hflow.1.1]
    exact localizedFlow_hMat_fixedTime_contDiffOn hflow 0 le_rfl y a b
  have hp := griffithsPositive_ricci_quadratic_pos X.metric.form
    (localizedFlow_initial_griffithsPositive hflow) hg x η hη
  have hp' : 0 < (star v ⬝ᵥ (ricci (h 0) x *ᵥ v)).re := by
    simpa only [η, WithLp.ofLp_toLp, hflow.1.1] using hp
  exact Complex.pos_iff.mpr ⟨hp', (hherm.im_star_dotProduct_mulVec_self v).symm⟩

end Yau.NodeProofs.C01Aux

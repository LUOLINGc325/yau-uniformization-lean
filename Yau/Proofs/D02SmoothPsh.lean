import Yau.Proofs.D02RealPshConversion
import Yau.Proofs.P02CircleSupports

/-! Smooth nonnegative Levi form implies the original circle-majorant psh
predicate. The support is the actual function itself. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false

theorem smoothLevi_isPshOn_chart {n : ℕ} {M : ComplexManifold n}
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (hL : ∀ y, (levi u y).PosSemidef)
    (x : M.Carrier) :
    IsPshOn (fun z => (inChart (α := ℝ) x u z : EReal)) (chartTarget x) := by
  apply isPshOn_of_complexLinePshOn
  apply P02Aux.complexLinePshOn_of_lower_supports (chartTarget x) (inChart x u) (hu x).continuousOn
  intro a ha
  refine ⟨inChart x u, ?_, rfl, Filter.Eventually.of_forall (fun _ => le_rfl), ?_⟩
  · exact ((hu x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds ha)).of_le (by simp)
  · intro v
    exact smoothFn_leviQuadratic_nonneg_in_chart hu hL x ha v

theorem smoothLevi_isPsh {n : ℕ} {M : ComplexManifold n}
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (hL : ∀ y, (levi u y).PosSemidef) :
    IsPsh (fun y => (u y : EReal)) := by
  refine ⟨fun y => EReal.coe_lt_top _,
    (continuous_coe_real_ereal.comp (L18Aux.continuous_of_smoothFn hu)).upperSemicontinuous, ?_⟩
  intro x z w hdisc φ hφ hmajor
  exact (smoothLevi_isPshOn_chart hu hL x).2.2 z w hdisc φ hφ hmajor

theorem immersionDifferentialNormSq_isPsh {n N : ℕ} (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F) :
    IsPsh (fun y => (immersionDifferentialNormSq X.metric.form F y : EReal)) :=
  smoothLevi_isPsh (immersionDifferentialNormSq_smooth X.metric.form
    (L12Aux.metricSmooth_of_smoothMetric X.metric) hF)
    (immersionDifferentialNormSq_levi_posSemidef X hF)

theorem immersionPotential_isPsh {n N : ℕ} (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F) :
    IsPsh (fun y => (immersionPotential X.metric.form F y : EReal)) :=
  smoothLevi_isPsh (immersionPotential_smooth X.metric.form
    (L12Aux.metricSmooth_of_smoothMetric X.metric) hF hImm)
    (immersionPotential_levi_posSemidef X hF hImm)

end Yau.NodeProofs.D02Aux

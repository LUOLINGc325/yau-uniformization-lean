import Yau.Proofs.F01AmbientOpenInverse
import Yau.Proofs.F01NormalCurvatureSign
import Yau.Proofs.F01MixedJetLocality

/-! The normal-chart curvature sign on the actual open component is
inherited from the ambient Kähler metric; no complete restricted metric is introduced. -/
noncomputable section
open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} (M : ComplexManifold n) (S : Opens M.Carrier)
  (hS : IsConnected (S : Set M.Carrier))

theorem restricted_normal_metric_mixed_nonpos (g : SmoothMetric M)
    (hcurv : NonnegBisectional g.form)
    (e : OpenPartialHomeomorph (ComplexVector n) (openConnectedManifold M S hS).Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (hs0 : (0 : ComplexVector n) ∈ e.source)
    (hzero : ∀ a b, fderiv ℝ (fun w =>
      Yau.LeafProofs.L17Aux.pullbackMatrix (openRestrictedField M S hS g.form) e w a b) 0 = 0)
    (i a : Fin n) :
    (wirt (fun w => wirtBar (fun y =>
      Yau.LeafProofs.L17Aux.pullbackMatrix (openRestrictedField M S hS g.form) e y a a)
        w (stdVec i)) 0 (stdVec i)).re ≤ 0 := by
  let E := ambientOpenChart M S hS e
  have hE := ambientOpenChart_mdifferentiableOn M S hS e he
  have hEi := ambientOpenChart_symm_mdifferentiableOn M S hS e hei
  have hsE : (0 : ComplexVector n) ∈ E.source := by
    change (0 : ComplexVector n) ∈ (ambientOpenChart M S hS e).source
    rw [ambientOpenChart_source]
    exact hs0
  have heq (a b : Fin n) : EqOn
      (fun w => Yau.LeafProofs.L17Aux.pullbackMatrix (openRestrictedField M S hS g.form) e w a b)
      (fun w => Yau.LeafProofs.L17Aux.pullbackMatrix g.form E w a b) e.source := by
    intro w hw
    exact congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A a b)
      (ambientOpenChart_pullbackMatrix M S hS g.form e he hw)
  have hEzero (a b : Fin n) :
      fderiv ℝ (fun w => Yau.LeafProofs.L17Aux.pullbackMatrix g.form E w a b) 0 = 0 := by
    have hgerm := Filter.eventuallyEq_of_mem (e.open_source.mem_nhds hs0) (heq a b)
    exact hgerm.fderiv_eq.symm.trans (hzero a b)
  have hh := normal_metric_mixed_nonpos g.form
    (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric g) hcurv E hE hEi hsE hEzero i a
  rw [mixed_wirtinger_eq_of_eqOn e.open_source (heq a a) hs0 (stdVec i) (stdVec i)]
  exact hh

end Yau.NodeProofs.F01Aux

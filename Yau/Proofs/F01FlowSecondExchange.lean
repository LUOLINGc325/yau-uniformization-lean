import Yau.Proofs.F01FlowDerivativeExchanges
import Yau.Proofs.F01ConformalSecondJets

/-! The paper's actual conformal-flow diagonal second-derivative exchange:
the Kähler background jets cancel and only the scalar conformal Hessians remain. -/
noncomputable section
open Set TopologicalSpace
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} (M : ComplexManifold n) (S : Opens M.Carrier)
  (hS : IsConnected (S : Set M.Carrier))

theorem conformal_flow_diagonal_second_exchange (g : SmoothMetric M)
    (f u : (openConnectedManifold M S hS).Carrier → ℝ) (hf : SmoothFn f) (hu : SmoothFn u)
    (k : HermitianField (openConnectedManifold M S hS)) (hk : MetricSmooth k) (t : ℝ)
    (hpot : ∀ x, gMat k x = gMat (conformalField (openRestrictedField M S hS g.form) f) x -
      (t : ℂ) • ricci (conformalField (openRestrictedField M S hS g.form) f) x + levi u x)
    (e : OpenPartialHomeomorph (ComplexVector n) (openConnectedManifold M S hS).Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (hs0 : (0 : ComplexVector n) ∈ e.source)
    (hvalue : pullbackMatrix (openRestrictedField M S hS g.form) e 0 = 1)
    (hjet : ∀ i j, fderiv ℝ (fun w =>
      pullbackMatrix (openRestrictedField M S hS g.form) e w i j) 0 = 0) (i a : Fin n) :
    wirt (fun w => wirtBar (fun y => pullbackMatrix k e y i i) w (stdVec a)) 0 (stdVec a) -
        wirt (fun w => wirtBar (fun y => pullbackMatrix k e y a a) w (stdVec i)) 0 (stdVec i) =
      leviC (fun w => Real.exp (f (e w))) 0 a a - leviC (fun w => Real.exp (f (e w))) 0 i i := by
  let g0 := openRestrictedField M S hS g.form
  let α := conformalField g0 f
  have hα : MetricSmooth α := conformalField_metricSmooth
    (openRestrictedField_metricSmooth M S hS (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric g)) hf
  exact (metric_potential_second_jet_exchange α k hα hk u hu t hpot e he hei hs0 i a).trans
    (conformal_normal_diagonal_mixed_exchange M S hS g f hf e he hs0 hvalue hjet i a)

end Yau.NodeProofs.F01Aux

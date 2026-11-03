import Yau.Proofs.F01FlowDerivativeExchanges
import Yau.Proofs.F01ConformalFirstJets

/-! The off-diagonal first derivative exchange includes the actual
conformal scalar error, in the constructed normal coordinate direction. -/
noncomputable section
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem conformal_flow_offdiagonal_first_exchange (g k : HermitianField M)
    (hg : MetricSmooth g) (hk : MetricSmooth k)
    (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (u : M.Carrier → ℝ) (hu : SmoothFn u) (t : ℝ)
    (hpot : ∀ x, gMat k x = gMat (conformalField g f) x -
      (t : ℂ) • ricci (conformalField g f) x + levi u x)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (hs0 : (0 : ComplexVector n) ∈ e.source) (hvalue : pullbackMatrix g e 0 = 1)
    (hjet : ∀ i j, fderiv ℝ (fun w => pullbackMatrix g e w i j) 0 = 0)
    (i a : Fin n) (hia : i ≠ a) :
    wirt (fun w => pullbackMatrix k e w a i) 0 (stdVec a) =
      wirt (fun w => pullbackMatrix k e w a a) 0 (stdVec i) -
        (Real.exp (f (e 0)) : ℂ) * wirt (fun w => (f (e w) : ℂ)) 0 (stdVec i) := by
  have hh := metric_potential_first_jet_exchange (conformalField g f) k
    (conformalField_metricSmooth hg hf) hk u hu t hpot e he hei hs0 a i a
  rw [conformal_normal_first_jet g hg f hf e he hs0 hvalue hjet a i (stdVec a),
    conformal_normal_first_jet g hg f hf e he hs0 hvalue hjet a a (stdVec i)] at hh
  simp only [Matrix.one_apply_ne hia.symm, Matrix.one_apply_eq, mul_zero, mul_one, zero_sub] at hh
  linear_combination hh

end Yau.NodeProofs.F01Aux

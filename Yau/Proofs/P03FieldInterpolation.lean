import Yau.Proofs.P03FiniteTopInterpolation
import Yau.Proofs.P03InterpolationData
import Yau.Proofs.P03InterpolationBundles
import Yau.Proofs.P03TopFormInverse

open scoped Manifold Topology ContDiff
open Set Filter MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar
open scoped CoefficientNorms CoefficientBundles

/-- The second original finite interpolation clause, for actual tangent
fields and the original vector-valued polynomial jets in every dimension. -/
theorem field_finite_interpolation {n : ℕ} (X : KahlerManifold n)
    (pts : Finset X.manifold.Carrier) (order : ℕ)
    (Pj : X.manifold.Carrier → Fin n → MvPolynomial (Fin n) ℂ) :
    ∃ V : VectorField X.manifold, IsHolomorphicField V ∧
      ∀ p ∈ pts, JetAgreeField V p (Pj p) order := by
  obtain ⟨μ, ψ, hμ, hψ⟩ := exists_interpolation_background X
  obtain ⟨hE, hh, hN⟩ := tangentAntiCanonical_interpolation_bundle X
  obtain ⟨w, hw, hjets⟩ := exists_finite_top_interpolation (r := n)
    (TangentAntiCanonicalFiber X.manifold) X.metric μ hμ (tangentAntiCanonicalMetric X.metric.form)
    hh hE hN ψ hψ pts Pj order
  let V := tangentAntiTopToField w
  refine ⟨V, tangentAntiTopToField_holomorphic w hw, ?_⟩
  intro p hp j hj
  have heq : fieldCoords V p =ᶠ[𝓝 (chartPt p p)]
      (fun z => coefficients (r := n) (TangentAntiCanonicalFiber X.manifold) w p z Fin.elim0) := by
    filter_upwards [(isOpen_extChartAt_target p).mem_nhds (mem_extChartAt_target p)] with z hz
    have hc := fieldToTangentAntiTop_coefficients V p hz
    rw [show fieldToTangentAntiTop V = w from fieldToTangentAntiTop_tangentAntiTopToField w] at hc
    exact hc.symm
  have hd := ((heq.sub (EventuallyEq.rfl (f := fun z : ComplexVector n => WithLp.toLp 2
    (fun α => MvPolynomial.eval (fun i => z i - chartPt p p i) (Pj p α))))).iteratedFDeriv ℂ j).self_of_nhds
  exact hd.trans (hjets p hp j hj)

end Yau.NodeProofs.P03Aux

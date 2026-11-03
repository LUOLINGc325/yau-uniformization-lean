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

/-- The first original finite interpolation clause, with its native
centred scalar polynomial jets at every order. -/
theorem scalar_finite_interpolation {n : ℕ} (X : KahlerManifold n)
    (pts : Finset X.manifold.Carrier) (order : ℕ)
    (Pj : X.manifold.Carrier → MvPolynomial (Fin n) ℂ) :
    ∃ f : X.manifold.Carrier → ℂ, IsHolomorphicFn f ∧
      ∀ p ∈ pts, JetAgreeFn f p (Pj p) order := by
  obtain ⟨μ, ψ, hμ, hψ⟩ := exists_interpolation_background X
  obtain ⟨hE, hh, hN⟩ := antiCanonical_interpolation_bundle X
  obtain ⟨w, hw, hjets⟩ := exists_finite_top_interpolation (r := 1)
    (AntiCanonicalFiber X.manifold) X.metric μ hμ (antiCanonicalMetric X.metric.form)
    hh hE hN ψ hψ pts (fun p _ => Pj p) order
  let f := antiTopToScalar w
  refine ⟨f, antiTopToScalar_holomorphic w hw, ?_⟩
  intro p hp j hj
  let F : ComplexVector n → ComplexVector 1 := fun z =>
    coefficients (r := 1) (AntiCanonicalFiber X.manifold) w p z Fin.elim0 -
      WithLp.toLp 2 (fun _ : Fin 1 => MvPolynomial.eval (fun i => z i - chartPt p p i) (Pj p))
  have heq : (scalarLineEquiv.symm ∘ F) =ᶠ[𝓝 (chartPt p p)]
      (fun z => inChart p f z - MvPolynomial.eval (fun i => z i - chartPt p p i) (Pj p)) := by
    filter_upwards [(isOpen_extChartAt_target p).mem_nhds (mem_extChartAt_target p)] with z hz
    change coefficients (r := 1) (AntiCanonicalFiber X.manifold) w p z Fin.elim0 0 -
      MvPolynomial.eval (fun i => z i - chartPt p p i) (Pj p) = _
    have hc := scalarToAntiTop_coefficients f p hz 0
    rw [show scalarToAntiTop f = w from scalarToAntiTop_antiTopToScalar w] at hc
    rw [hc]
  have hd := scalarLineEquiv.symm.iteratedFDeriv_comp_left (f := F) (x := chartPt p p) (i := j)
  have hj0 : iteratedFDeriv ℂ j F (chartPt p p) = 0 := hjets p hp j hj
  rw [hj0] at hd
  have hd0 : iteratedFDeriv ℂ j (scalarLineEquiv.symm ∘ F) (chartPt p p) = 0 := by
    calc
      _ = scalarLineEquiv.symm.toContinuousLinearMap.compContinuousMultilinearMap 0 := hd
      _ = 0 := by
        ext args
        exact scalarLineEquiv.symm.map_zero
  exact ((heq.iteratedFDeriv ℂ j).self_of_nhds).symm.trans hd0

end Yau.NodeProofs.P03Aux

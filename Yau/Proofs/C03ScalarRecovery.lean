import Yau.Proofs.C03ScalarRecoveryModel
import Yau.Proofs.C03ScalarRecoveryJet

/-! One entire scalar complement preserves every actual weighted correction norm at once. -/
noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff Manifold ENNReal
namespace Yau.Proofs.C03Aux.ScalarRecovery
open Yau Yau.LeafProofs L14Aux Yau.Proofs.P04Aux BundleDbar
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false

theorem exists_entire_scalar_complement (hn : 1 ≤ n)
    (s u : NQForm (CanonicalCoefficients (ComplexEuclideanManifold n hn)) 0)
    (f : NQForm (CanonicalCoefficients (ComplexEuclideanManifold n hn)) 1)
    (hs : WeakDbar (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn)) s f)
    (hu : WeakDbar (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn)) u f) :
    ∃ w : NQForm (CanonicalCoefficients (ComplexEuclideanManifold n hn)) 0,
      HolomorphicTopForm (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn)) w ∧
      Differentiable ℂ (scalarCoefficient hn w) ∧
      (scalarCoefficient hn s - scalarCoefficient hn w =ᵐ[
        (volume : Measure (ComplexVector n))] scalarCoefficient hn u) ∧
      ∀ ψ : ComplexVector n → ℝ, SmoothFn (M := ComplexEuclideanManifold n hn) ψ →
        weightedNormSq (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn))
          (FlatComplete.euclideanCompleteMetric n hn).form flatMetric
          (FlatComplete.euclideanVolume n hn) ψ u =
          ENNReal.ofReal ((2 : ℝ) ^ n) * ∫⁻ z,
            ENNReal.ofReal (‖scalarCoefficient hn s z - scalarCoefficient hn w z‖ ^ 2 *
              Real.exp (-ψ z)) ∂(volume : Measure (ComplexVector n)) := by
  obtain ⟨w, hw, heq, hL, hnorm⟩ := Yau.NodeProofs.P03Aux.exists_holomorphic_complement
    (CanonicalCoefficients (ComplexEuclideanManifold n hn))
    (FlatComplete.euclideanCompleteMetric n hn) (FlatComplete.euclideanVolume n hn)
    (FlatComplete.euclideanCompleteMetric_volume n hn) coefficient_holomorphic s u f hs hu
  refine ⟨w, hw, scalarCoefficient_differentiable hn w hw, ?_, ?_⟩
  · have hc := coefficients_ae_eq_of_ae_eq
      (CanonicalCoefficients (ComplexEuclideanManifold n hn))
      (FlatComplete.euclideanCompleteMetric n hn) (FlatComplete.euclideanVolume n hn)
      (FlatComplete.euclideanCompleteMetric_volume n hn) (subForm _ s w) u heq
      (0 : ComplexVector n) Fin.elim0 (0 : Fin 1)
    rw [source_localDomain hn, Measure.restrict_univ, lebesgueC_eq_volume] at hc
    change scalarCoefficient hn (subForm _ s w) =ᵐ[volume] scalarCoefficient hn u at hc
    rwa [scalarCoefficient_sub] at hc
  · intro ψ hψ
    rw [← hnorm flatMetric ψ, weightedNormSq_scalar hn (subForm _ s w) hL ψ hψ,
      scalarCoefficient_sub]
    rfl

end Yau.Proofs.C03Aux.ScalarRecovery

import Yau.Proofs.P03FiniteHolomorphicApproximation
import Yau.Proofs.P03TopPolynomialJets

open scoped Manifold Topology ContDiff ENNReal
open Set Filter MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- Genuine finite interpolation of actual coefficient jets on a bundle
with its actual smooth holomorphic atlas and computed Nakano metric. -/
theorem exists_finite_top_interpolation (g : Yau.SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : Metric (M := M) E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (hE : Holomorphic (r := r) E) (hN : NakanoNonnegative (r := r) E h)
    (ψ : M.Carrier → ℝ) (hψ : IsSmoothStrictPsh ψ)
    (pts : Finset M.Carrier) (Pj : M.Carrier → Fin r → MvPolynomial (Fin n) ℂ) (order : ℕ) :
    ∃ w : NQForm E 0, HolomorphicTopForm (r := r) E w ∧
      ∀ p ∈ pts, ∀ j ≤ order, iteratedFDeriv ℂ j
        (fun z => coefficients (r := r) E w p z Fin.elim0 -
          WithLp.toLp 2 (fun α => MvPolynomial.eval (fun i => z i - chartPt p p i) (Pj p α)))
        (chartPt p p) = 0 := by
  obtain ⟨w, v, b, k, B, hw, hv, hgerm, hb, hk, hB, hbase, hnorm, hsing⟩ :=
    exists_finite_holomorphic_approximation E g μ hμ h hh hE hN ψ hψ pts Pj order
  let Φ : M.Carrier → ℝ := fun x => k * ψ x
  have hΦ : SmoothFn Φ := fun a => contDiffOn_const.mul (hψ.1 a)
  have hcur : ∀ j : ℕ, weightedNormSq (r := r) E g.form h μ
      (fun x => Φ x + finitePolePerturbation (fun p : pts => p.1) b (n + order + 1 : ℕ) j x) v ≤
        ENNReal.ofReal B := by
    intro j
    have hj := hnorm j
    change weightedNormSq (r := r) E g.form h μ
      (fun x => k * ψ x + finitePolePerturbation (fun p : pts => p.1) b
        ((n : ℝ) + order + 1) j x) v ≤ ENNReal.ofReal B at hj
    simpa only [Φ, Nat.cast_add, Nat.cast_one] using hj
  have hz := top_coefficient_pole_jets_zero E g μ hμ h hh Φ hΦ pts b (fun p => (hb p).2)
    order w v hw hv Pj hgerm B (by linarith) hcur
  refine ⟨w, hw, ?_⟩
  intro p hp
  exact top_polynomial_jets_of_correction_zero E w v hw p (Pj p) order (hgerm p hp) (hz p hp)

end Yau.NodeProofs.P03Aux

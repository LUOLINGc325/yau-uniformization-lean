import Yau.Proofs.P03SinglePoleCoefficientBounds
import Yau.Proofs.P03RegularizedPoleDecay
import Yau.Proofs.P03LocalHolomorphicJets
import Yau.Proofs.P03Polynomials

open scoped Manifold Topology ContDiff ENNReal
open Set Filter MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar Yau.LeafProofs.L14Aux

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- Polynomial-minus-holomorphic correction germs with the original pole
estimates have zero actual complex coefficient jets at every specified point. -/
theorem top_coefficient_pole_jets_zero (g : Yau.SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : Metric (M := M) E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (Φ : M.Carrier → ℝ) (hΦ : SmoothFn Φ) (pts : Finset M.Carrier)
    (b : ∀ p : pts, SmoothBumpFunction 𝓘(ℝ, ComplexVector n) p.1)
    (hs : ∀ p : pts, tsupport (b p : M.Carrier → ℝ) ⊆ {x | x ∈ pts ∧ x ≠ p.1}ᶜ)
    (order : ℕ) (w v : NQForm E 0) (hw : HolomorphicTopForm (r := r) E w)
    (hv : LocallyL2 (r := r) E v)
    (Pj : M.Carrier → Fin r → MvPolynomial (Fin n) ℂ)
    (hgerm : ∀ p ∈ pts, (fun z => coefficients (r := r) E v p z Fin.elim0) =ᶠ[𝓝 (chartPt p p)]
      (fun z => WithLp.toLp 2 (fun α => MvPolynomial.eval (fun i => z i - chartPt p p i) (Pj p α)) -
        coefficients (r := r) E w p z Fin.elim0))
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ j : ℕ, weightedNormSq (r := r) E g.form h μ
      (fun x => Φ x + finitePolePerturbation (fun p : pts => p.1) b (n + order + 1 : ℕ) j x) v ≤
        ENNReal.ofReal B) :
    ∀ p ∈ pts, ∀ α : Fin r, ∀ j ≤ order,
      iteratedFDeriv ℂ j (fun z => coefficients (r := r) E v p z Fin.elim0 α) (chartPt p p) = 0 := by
  intro p hp α
  let q : pts := ⟨p, hp⟩
  obtain ⟨R, D, hR, hD, hK, hcoef⟩ := exists_single_pole_coefficient_bound E g μ hμ h hh Φ hΦ pts b hs
    (n + order + 1) v hv B hB hb q α
  let f : ComplexVector n → ℂ := fun z => coefficients (r := r) E v p z Fin.elim0 α
  have hm : AEStronglyMeasurable f ((volume : Measure (ComplexVector n)).restrict
      (Metric.closedBall (chartPt p p) R)) := by
    rw [← actualMeasure_eq_volume n]
    exact (hv p Fin.elim0 α).1.mono_measure (Measure.restrict_mono hK le_rfl)
  have hdecay := L2_decay_of_regularized_pole_bounds f (chartPt p p) R hR (n + order + 1) hm D hD hcoef
  let Q : ComplexVector n → ℂ := fun z => MvPolynomial.eval (fun i => z i - chartPt p p i) (Pj p α) -
    coefficients (r := r) E w p z Fin.elim0 α
  have hQ : DifferentiableOn ℂ Q (localDomain (r := r) E p) :=
    (centeredPolynomial_differentiable (Pj p α) (chartPt p p)).differentiableOn.sub (hw p α)
  have heq : f =ᶠ[𝓝 (chartPt p p)] Q := (hgerm p hp).mono fun z hz => by
    have he := congrArg (fun z : ComplexVector r => z α) hz
    simpa only [PiLp.sub_apply, PiLp.toLp_apply] using he
  have hself : chartPt p p ∈ localDomain (r := r) E p :=
    chartPt_mem_localDomain E p p ⟨mem_extChartAt_source p, FiberBundle.mem_baseSet_trivializationAt' p⟩
  have hn := inter_mem ((localDomain_isOpen E p).mem_nhds hself) heq
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.mp hn
  have hf : DifferentiableOn ℂ f (Metric.ball (chartPt p p) δ) :=
    (hQ.mono (fun z hz => (hδs hz).1)).congr (fun z hz => (hδs hz).2)
  exact complex_jets_zero_of_L2_decay Metric.isOpen_ball f hf (chartPt p p)
    (Metric.mem_ball_self hδ) R hR order ((2 : ℝ) ^ (n + order + 1) * D) (by positivity) hdecay

end Yau.NodeProofs.P03Aux

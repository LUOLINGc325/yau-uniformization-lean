import Yau.Proofs.P03FiniteJetSourceData
import Yau.Proofs.P03OneRegularizedSolution
import Yau.Proofs.P03SingularNormBounds

open scoped Manifold Topology ContDiff
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

/-- One correction solves the actual finite polynomial seed's Dolbeault
equation and has a finite singular norm. All weights use one fixed metric
and one fixed background multiplier. -/
theorem exists_finite_jet_corrector (g : Yau.SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : Metric (M := M) E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (hE : Holomorphic (r := r) E) (hN : NakanoNonnegative (r := r) E h)
    (ψ : M.Carrier → ℝ) (hψ : IsSmoothStrictPsh ψ)
    (pts : Finset M.Carrier) (Pj : M.Carrier → Fin r → MvPolynomial (Fin n) ℂ) (order : ℕ) :
    ∃ (s : NQForm E 0) (f : NQForm E 1)
      (b : ∀ p : pts, SmoothBumpFunction 𝓘(ℝ, ComplexVector n) p.1) (k B : ℝ)
      (u : NQForm E 0),
      SmoothForm (r := r) E s ∧ SmoothForm (r := r) E f ∧
      WeakDbar (r := r) E s f ∧ WeakDbar (r := r) E u f ∧
      (∀ p ∈ pts,
        ((fun z => coefficients (r := r) E s p z Fin.elim0) =ᶠ[𝓝 (chartPt p p)]
          (fun z => WithLp.toLp 2 (fun α =>
            MvPolynomial.eval (fun i => z i - chartPt p p i) (Pj p α)))) ∧
        p ∉ closure {x | f x ≠ (0 : NQForm E 1) x}) ∧
      (∀ p : pts, (b p).rOut ≤ 1 / 2 ∧
        tsupport (b p : M.Carrier → ℝ) ⊆ {x | x ∈ pts ∧ x ≠ p.1}ᶜ) ∧
      1 ≤ k ∧ 1 ≤ B ∧
      WeightedL2 (r := r) E g.form h μ (fun x => k * ψ x) u ∧
      (∀ j, weightedNormSq (r := r) E g.form h μ
        (finitePoleWeight ψ k ((n : ℝ) + order + 1) (fun p : pts => p.1) b j) u ≤ ENNReal.ofReal B) ∧
      (∫⁻ x, singularTopIntegrand (r := r) E g.form h
        (finitePoleWeight ψ k ((n : ℝ) + order + 1) (fun p : pts => p.1) b) u x ∂μ) ≤ ENNReal.ofReal B := by
  classical
  obtain ⟨s, f, b, k, B, hs, hf, hsf, hclosed, hfc, hgerm, hb, hk, hB, hm, hweights⟩ :=
    exists_finite_jet_source_data E g μ hμ h hh hE hN ψ hψ pts Pj order
  let c : ℝ := (n : ℝ) + order + 1
  let Φ : M.Carrier → ℝ := fun x => k * ψ x
  let p := finitePolePerturbation (fun p : pts => p.1) b c
  have hΦ : SmoothFn Φ := fun a => contDiffOn_const.mul (hψ.1 a)
  have hbase : WeightedL2 (r := r) E g.form h μ Φ f :=
    smooth_compact_weightedL2_one E g μ hμ h hh Φ hΦ f hf hfc
  obtain ⟨u, huf, hu, hub⟩ := one_solution_all_regularized_bounds E g μ hμ h hh hE Φ hΦ p
    (finitePolePerturbation_smooth _ b c) (finitePolePerturbation_compactSupport _ b c)
    (finitePolePerturbation_nonpos _ b (fun q => (hb q).1) c (by dsimp [c]; positivity))
    (finitePolePerturbation_antitone _ b c (by dsimp [c]; positivity)) f hclosed hbase
    (fun j => (hweights j).2.1) B (by linarith) (fun j => (hweights j).2.2.2)
  refine ⟨s, f, b, k, B, u, hs, hf, hsf, huf, hgerm, hb, hk, hB, hu, hub, ?_⟩
  exact singularTopIntegrand_lintegral_le E g μ hμ h hh _
    (fun j => (hweights j).1.1) hm u hu.1 B hub

end Yau.NodeProofs.P03Aux

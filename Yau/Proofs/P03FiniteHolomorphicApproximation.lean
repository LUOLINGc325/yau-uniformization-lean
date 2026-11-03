import Yau.Proofs.P03FiniteJetCorrector
import Yau.Proofs.P03HolomorphicCorrection

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

/-- A genuine global holomorphic top form differs from each prescribed
polynomial germ by one correction with finite singular weighted norm. -/
theorem exists_finite_holomorphic_approximation (g : Yau.SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : Metric (M := M) E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (hE : Holomorphic (r := r) E) (hN : NakanoNonnegative (r := r) E h)
    (ψ : M.Carrier → ℝ) (hψ : IsSmoothStrictPsh ψ)
    (pts : Finset M.Carrier) (Pj : M.Carrier → Fin r → MvPolynomial (Fin n) ℂ) (order : ℕ) :
    ∃ (w v : NQForm E 0)
      (b : ∀ p : pts, SmoothBumpFunction 𝓘(ℝ, ComplexVector n) p.1) (k B : ℝ),
      HolomorphicTopForm (r := r) E w ∧ LocallyL2 (r := r) E v ∧
      (∀ p ∈ pts,
        (fun z => coefficients (r := r) E v p z Fin.elim0) =ᶠ[𝓝 (chartPt p p)]
          (fun z => WithLp.toLp 2 (fun α =>
            MvPolynomial.eval (fun i => z i - chartPt p p i) (Pj p α)) -
              coefficients (r := r) E w p z Fin.elim0)) ∧
      (∀ p : pts, (b p).rOut ≤ 1 / 2 ∧
        tsupport (b p : M.Carrier → ℝ) ⊆ {x | x ∈ pts ∧ x ≠ p.1}ᶜ) ∧
      1 ≤ k ∧ 1 ≤ B ∧
      WeightedL2 (r := r) E g.form h μ (fun x => k * ψ x) v ∧
      (∀ j, weightedNormSq (r := r) E g.form h μ
        (finitePoleWeight ψ k ((n : ℝ) + order + 1) (fun p : pts => p.1) b j) v ≤ ENNReal.ofReal B) ∧
      (∫⁻ x, singularTopIntegrand (r := r) E g.form h
        (finitePoleWeight ψ k ((n : ℝ) + order + 1) (fun p : pts => p.1) b) v x ∂μ) ≤ ENNReal.ofReal B := by
  obtain ⟨s, f, b, k, B, u, hs, hf, hsf, huf, hgerm, hb, hk, hB, hu, hub, hsing⟩ :=
    exists_finite_jet_corrector E g μ hμ h hh hE hN ψ hψ pts Pj order
  obtain ⟨w, hw, hae, hlocal, hnorm⟩ := exists_holomorphic_complement E g μ hμ hE s u f hsf huf
  let v := subForm E s w
  refine ⟨w, v, b, k, B, hw, hlocal, ?_, hb, hk, hB, ?_, ?_, ?_⟩
  · intro p hp
    filter_upwards [(hgerm p hp).1] with z hz
    ext α : 1
    rw [PiLp.sub_apply, coefficients_subForm]
    exact congrArg (fun t : ComplexVector r => t α - coefficients (r := r) E w p z Fin.elim0 α) hz
  · exact weightedL2_of_ae_eq E g μ hμ h (fun x => k * ψ x) u v hu
      (hae.mono fun _ hx => hx.symm)
  · intro j
    exact (hnorm h _).le.trans (hub j)
  · rw [lintegral_congr_ae (singularTopIntegrand_congr_ae E g.form h μ _ v u hae)]
    exact hsing

end Yau.NodeProofs.P03Aux

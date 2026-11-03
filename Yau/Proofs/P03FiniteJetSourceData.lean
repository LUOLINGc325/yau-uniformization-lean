import Yau.Proofs.P03FiniteTopJetSeeds
import Yau.Proofs.P03PoleBumps
import Yau.Proofs.P03RegularizedSourceBounds

open scoped Manifold Topology ContDiff
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

/-- Actual finite polynomial germs give one compact closed source and one
entire regularized pole system, with the strict multiplier and finite
inverse-curvature constant chosen before all regularization indices. -/
theorem exists_finite_jet_source_data (g : Yau.SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : Metric (M := M) E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (hE : Holomorphic (r := r) E) (hN : NakanoNonnegative (r := r) E h)
    (ψ : M.Carrier → ℝ) (hψ : IsSmoothStrictPsh ψ)
    (pts : Finset M.Carrier) (Pj : M.Carrier → Fin r → MvPolynomial (Fin n) ℂ) (order : ℕ) :
    ∃ (s : NQForm E 0) (f : NQForm E 1)
      (b : ∀ p : pts, SmoothBumpFunction 𝓘(ℝ, ComplexVector n) p.1) (k B : ℝ),
      SmoothForm (r := r) E s ∧ SmoothForm (r := r) E f ∧
      WeakDbar (r := r) E s f ∧ WeaklyClosed (r := r) E f ∧
      IsCompact (closure {x | f x ≠ (0 : NQForm E 1) x}) ∧
      (∀ p ∈ pts,
        ((fun z => coefficients (r := r) E s p z Fin.elim0) =ᶠ[𝓝 (chartPt p p)]
          (fun z => WithLp.toLp 2 (fun α =>
            MvPolynomial.eval (fun i => z i - chartPt p p i) (Pj p α)))) ∧
        p ∉ closure {x | f x ≠ (0 : NQForm E 1) x}) ∧
      (∀ p : pts, (b p).rOut ≤ 1 / 2 ∧
        tsupport (b p : M.Carrier → ℝ) ⊆ {x | x ∈ pts ∧ x ≠ p.1}ᶜ) ∧
      1 ≤ k ∧ 1 ≤ B ∧
      (∀ x, Antitone (fun j => finitePoleWeight ψ k ((n : ℝ) + order + 1)
        (fun p : pts => p.1) b j x)) ∧
      ∀ j : ℕ,
        IsSmoothStrictPsh (finitePoleWeight ψ k ((n : ℝ) + order + 1) (fun p : pts => p.1) b j) ∧
        WeightedNakanoNonnegative (r := r) E h
          (finitePoleWeight ψ k ((n : ℝ) + order + 1) (fun p : pts => p.1) b j) ∧
        (∀ x, finitePoleWeight ψ k ((n : ℝ) + order + 1) (fun p : pts => p.1) b j x ≤ k * ψ x) ∧
        inverseCurvatureIntegral (r := r) E g.form h μ
          (finitePoleWeight ψ k ((n : ℝ) + order + 1) (fun p : pts => p.1) b j) f ≤ ENNReal.ofReal B := by
  classical
  obtain ⟨s, f, hs, hf, hD, hw, hclosed, hsc, hfc, hgerm⟩ := exists_finite_top_jet_source E hE pts Pj
  have hU (p : pts) : {x : M.Carrier | x ∈ pts ∧ x ≠ p.1}ᶜ ∈ 𝓝 p.1 := by
    have hfin : Set.Finite {x : M.Carrier | x ∈ pts ∧ x ≠ p.1} :=
      pts.finite_toSet.subset (fun _ hx => hx.1)
    exact hfin.isClosed.isOpen_compl.mem_nhds (by simp)
  choose b hR hsupport using fun p : pts => exists_small_pole_bump p.1 (hU p)
  obtain ⟨k, B, hk, hB, hmono, hb⟩ := exists_regularized_source_bounds E g μ hμ h hh hN ψ hψ
    (fun p : pts => p.1) b hR ((n : ℝ) + order + 1) (by positivity) f hf hfc
    subset_closure (fun p => (hgerm p.1 p.2).2)
  exact ⟨s, f, b, k, B, hs, hf, hw, hclosed, hfc, hgerm,
    (fun p => ⟨hR p, hsupport p⟩), hk, hB, hmono, hb⟩

end Yau.NodeProofs.P03Aux

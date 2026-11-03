import Yau.Proofs.P03CompactSourceIntegral
import Yau.Proofs.P03FinitePoleStrictifier
import Yau.Proofs.P03WeightedNakano

open scoped Manifold Topology ContDiff
open Set MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar Yau.LeafProofs.L22Aux

variable {n r : ℕ} {M : ComplexManifold n} {ι : Type*} [Fintype ι]
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- One fixed metric, one background multiplier, and one finite source
bound work for the entire genuine finite-pole regularization sequence. -/
theorem exists_regularized_source_bounds (g : Yau.SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : Metric (M := M) E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (hN : NakanoNonnegative (r := r) E h)
    (ψ : M.Carrier → ℝ) (hψ : IsSmoothStrictPsh ψ)
    (a : ι → M.Carrier) (b : ∀ i, SmoothBumpFunction 𝓘(ℝ, ComplexVector n) (a i))
    (hR : ∀ i, (b i).rOut ≤ 1 / 2) (c : ℝ) (hc : 0 ≤ c)
    (f : NQForm E 1) (hf : SmoothForm (r := r) E f)
    {K : Set M.Carrier} (hK : IsCompact K) (hsupp : {x | f x ≠ (0 : NQForm E 1) x} ⊆ K)
    (hKa : ∀ i, a i ∉ K) :
    ∃ k B : ℝ, 1 ≤ k ∧ 1 ≤ B ∧
      (∀ x, Antitone (fun j => finitePoleWeight ψ k c a b j x)) ∧
      ∀ j : ℕ,
        IsSmoothStrictPsh (finitePoleWeight ψ k c a b j) ∧
        WeightedNakanoNonnegative (r := r) E h (finitePoleWeight ψ k c a b j) ∧
        (∀ x, finitePoleWeight ψ k c a b j x ≤ k * ψ x) ∧
        inverseCurvatureIntegral (r := r) E g.form h μ (finitePoleWeight ψ k c a b j) f ≤
          ENNReal.ofReal B := by
  obtain ⟨k, hk, hstrict, hdom⟩ := exists_finitePoleWeight_strictifier ψ hψ a b c hc
  let φ := finitePoleWeight ψ k c a b
  have hφN (j : ℕ) : WeightedNakanoNonnegative (r := r) E h (φ j) :=
    weightedNakano_of_nakano_strictPsh E h hN (φ j) (hstrict j)
  obtain ⟨lam, hlam, hinv⟩ := exists_compact_inverseCurvature_bound E g h hN ψ hψ φ
    (fun j => (hstrict j).1)
    (fun j x v => hdom j x (chartPt x x) (mem_extChartAt_target x) v) f hK
  obtain ⟨C, hC, hweight⟩ := exists_compact_finitePoleWeight_exp_upper ψ hψ.1 k c hc a b hK hKa
  obtain ⟨B, hB, hIB⟩ := exists_uniform_inverseCurvatureIntegral_bound E g μ hμ h hh φ hφN f hf
    hK hsupp lam hlam hinv C (by linarith) hweight
  refine ⟨k, B, hk, hB, finitePoleWeight_antitone ψ k c hc a b, ?_⟩
  intro j
  exact ⟨hstrict j, hφN j, finitePoleWeight_le_background ψ k c hc a b hR j, hIB j⟩

end Yau.NodeProofs.P03Aux

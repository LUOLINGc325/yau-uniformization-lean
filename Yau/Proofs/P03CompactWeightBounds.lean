import Yau.Proofs.P03CompactPoleBounds
import Yau.Proofs.P03FinitePoleWeights

open scoped Manifold Topology ContDiff
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.LeafProofs

variable {n : ℕ} {M : ComplexManifold n} {ι : Type*} [Fintype ι]

theorem exists_compact_finitePole_lower (a : ι → M.Carrier)
    (b : ∀ i, SmoothBumpFunction 𝓘(ℝ, ComplexVector n) (a i))
    (c : ℝ) (hc : 0 ≤ c) {K : Set M.Carrier} (hK : IsCompact K)
    (hKa : ∀ i, a i ∉ K) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ, ∀ x ∈ K, -D ≤ finitePolePerturbation a b c j x := by
  classical
  have hex (i : ι) := exists_compact_manifoldPole_lower (a i) (b i) c hc hK (hKa i)
  choose D hD hbound using hex
  refine ⟨∑ i, D i, Finset.sum_nonneg (fun i _ => hD i), ?_⟩
  intro j x hx
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hbound i j x hx)
  simpa only [finitePolePerturbation, Finset.sum_neg_distrib] using hs

/-- One finite exponential bound works on the compact source support for
all actual regularized finite-pole weights. -/
theorem exists_compact_finitePoleWeight_exp_upper (ψ : M.Carrier → ℝ) (hψ : SmoothFn ψ)
    (k c : ℝ) (hc : 0 ≤ c) (a : ι → M.Carrier)
    (b : ∀ i, SmoothBumpFunction 𝓘(ℝ, ComplexVector n) (a i))
    {K : Set M.Carrier} (hK : IsCompact K) (hKa : ∀ i, a i ∉ K) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ j : ℕ, ∀ x ∈ K,
      Real.exp (-finitePoleWeight ψ k c a b j x) ≤ B := by
  obtain ⟨D, hD, hbound⟩ := exists_compact_finitePole_lower a b c hc hK hKa
  have hbg : Continuous (fun x => k * ψ x) :=
    continuous_const.mul (L18Aux.continuous_of_smoothFn hψ)
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hbg.continuousOn
  refine ⟨max 1 (Real.exp (A + D)), le_max_left _ _, ?_⟩
  intro j x hx
  have hbgx := hA x hx
  change |k * ψ x| ≤ A at hbgx
  have hp := hbound j x hx
  have hexp : -finitePoleWeight ψ k c a b j x ≤ A + D := by
    have hn := (abs_le.mp hbgx).1
    dsimp only [finitePoleWeight]
    linarith
  exact (Real.exp_le_exp.mpr hexp).trans (le_max_right _ _)

end Yau.NodeProofs.P03Aux

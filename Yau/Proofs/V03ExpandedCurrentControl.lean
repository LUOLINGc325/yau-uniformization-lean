import Yau.Proofs.V03ExpandedCurrentAtoms
import Yau.Proofs.V03CurrentAtomContinuity

/-! The exact finite signed family inherits the same original uniform
constant and genuine angular continuity from its explicitly defined atoms. -/

open scoped Topology ContDiff Matrix
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n} {d : VariationData X q}
  {B : CotangentPoint X.manifold → Matrix (Fin q) (Fin q) ℂ}

theorem realizedExpandedAtom_continuous (hd : VariationSetup d) (j a : ℕ)
    (hB : ∀ x b c, ContDiffOn ℝ ∞ (fun z => B (cotangentChartInv x z) b c) (cotangentTarget x))
    (F : VariationDisc X) (hF : AdmissibleVariationDisc d j F)
    (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ) (h α : ℂ → ℂ)
    (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ)
    (hR : RealizesFirstField d j a F E l h α fz R) (t : CurrentExpansionIndex q) :
    Continuous (realizedExpandedAtom d B F E l h α t) := by
  change Continuous (fun θ => realizedExpandedAtom d B F E l h α t θ)
  have hc := realizedCurrentAtom_continuous hd j a hB F hF E l h α fz R hR
  cases t with
  | inl t =>
    rcases t with ⟨⟨⟨i, k⟩, c⟩, r⟩
    fin_cases r
    · simpa [realizedExpandedAtom, Fin.ext_iff] using
        hc (some i) (some k) (.inr ((i, k), (c, 0))) 1 (.inl c)
    · simpa [realizedExpandedAtom, Fin.ext_iff] using
        hc (some k) (some i) (.inr ((i, k), (c, 0))) 1 (.inl c)
    · simpa [realizedExpandedAtom, Fin.ext_iff] using
        hc (some i) (some k) (.inr ((i, k), (c, 1))) 0 (.inl c)
    · change Continuous (fun θ => -realizedCurrentAtom d B F E l h α
        (some k) (some i) (.inr ((i, k), (c, 1))) 0 (.inl c) θ)
      exact (hc (some k) (some i) (.inr ((i, k), (c, 1))) 0 (.inl c)).neg
  | inr t =>
    rcases t with ⟨⟨i, k⟩, r⟩
    fin_cases r
    · simpa [realizedExpandedAtom, Fin.ext_iff] using
        hc (some k) none (.inl (i, k)) 3 (.inr i)
    · simpa [realizedExpandedAtom, Fin.ext_iff] using
        hc (some i) none (.inl (i, k)) 1 (.inr k)

theorem realizedExpandedAtom_uniform_bound (hd : VariationSetup d) (j a : ℕ)
    (hB : ∀ x b c, ContDiffOn ℝ ∞ (fun z => B (cotangentChartInv x z) b c) (cotangentTarget x))
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : VariationDisc X) (E : ℂ → CotangentMatrix n)
      (l : ℂ → CotangentIndex n → ℂ) (h α : ℂ → ℂ)
      (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ),
      AdmissibleVariationDisc d j F → NormalizedDiscFrame d.G F.f E → HolomorphicColumn l →
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ∑ i, ‖l ζ i‖ ^ 2 ≤ L ^ 2) →
      RealizesFirstField d j a F E l h α fz R → ∀ t : CurrentExpansionIndex q,
      |∫ θ in (-Real.pi)..Real.pi, realizedExpandedAtom d B F E l h α t θ| ≤
        C * (1 + (variationEnergy d j F).toReal +
          (boundaryDSq (fun θ => l (circlePoint θ))).toReal) := by
  obtain ⟨C, hC, hb⟩ := realizedCurrentAtom_uniform_bound hd j a hB L hL
  refine ⟨C, hC, fun F E l h α fz R hF hE hl hlL hR t => ?_⟩
  have hh := hb F E l h α fz R hF hE hl hlL hR
  cases t with
  | inl t =>
    rcases t with ⟨⟨⟨i, k⟩, c⟩, r⟩
    fin_cases r
    · simpa [realizedExpandedAtom, Fin.ext_iff] using
        hh (some i) (some k) (.inr ((i, k), (c, 0))) 1 (.inl c)
    · simpa [realizedExpandedAtom, Fin.ext_iff] using
        hh (some k) (some i) (.inr ((i, k), (c, 0))) 1 (.inl c)
    · simpa [realizedExpandedAtom, Fin.ext_iff] using
        hh (some i) (some k) (.inr ((i, k), (c, 1))) 0 (.inl c)
    · simpa [realizedExpandedAtom, Fin.ext_iff, intervalIntegral.integral_neg] using
        hh (some k) (some i) (.inr ((i, k), (c, 1))) 0 (.inl c)
  | inr t =>
    rcases t with ⟨⟨i, k⟩, r⟩
    fin_cases r
    · simpa [realizedExpandedAtom, Fin.ext_iff] using
        hh (some k) none (.inl (i, k)) 3 (.inr i)
    · simpa [realizedExpandedAtom, Fin.ext_iff] using
        hh (some i) none (.inl (i, k)) 1 (.inr k)

end Yau.Blueprint.V03Proof

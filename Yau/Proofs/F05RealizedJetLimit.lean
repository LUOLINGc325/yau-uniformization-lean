import Yau.Proofs.F05CompatibleJetEvaluationLimit
import Yau.Proofs.F05CanonicalRealization
import Yau.Proofs.F05CanonicalContinuity
import Yau.Proofs.F05CanonicalBoundary

/-! The limiting compatible graph has an actual manifold representative,
with literal finite Schauder norm, genuine closed-face continuity and
traces, and pointwise convergence of all four evaluated jets. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_realized_jet_limit {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    {α T : ℝ} (hT : 0 < T) (u : ℕ → F05CompatibleJetGraph A α hT.le)
    (uLim : F05CompatibleJetGraph A α hT.le) (hu : Tendsto u atTop (𝓝 uLim)) :
    ∃ (W : M.Carrier → ℝ → ℝ) (K : ℝ), 0 < K ∧
      (∀ i, SchauderBound α (F05Q A i T) (pull A i W) K) ∧
      ContinuousOn (fun z : M.Carrier × ℝ => W z.1 z.2) (closure O ×ˢ Icc 0 T) ∧
      (∀ x, W x 0 = 0) ∧
      (∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, W x t = 0) ∧
      ∀ i (p : F05Q A i T),
        Tendsto (fun k => ((u k).val i).val.1 p) atTop (𝓝 (pull A i W p.val)) ∧
        Tendsto (fun k => ((u k).val i).val.2.1 p) atTop (𝓝 (spatialD (pull A i W) p.val)) ∧
        Tendsto (fun k => ((u k).val i).val.2.2.1.val.1 p) atTop
          (𝓝 (spatialDD (pull A i W) p.val)) ∧
        Tendsto (fun k => ((u k).val i).val.2.2.2.val.1 p) atTop
          (𝓝 (timeD (F05Q A i T) (pull A i W) p.val)) := by
  let W := F05CanonicalJetFunction A χ α hT.le uLim
  let K := ‖uLim‖+1
  have hSch (i : Fin A.count) : SchauderBound α (F05Q A i T) (pull A i W) K := by
    have hBound : ‖(uLim.val i).val‖ ≤ K := by
      have hh := norm_le_pi_norm uLim.val i
      change ‖uLim.val i‖ ≤ ‖uLim.val‖+1
      exact hh.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
    exact schauderBound_mono_const (F05CanonicalJetFunction_schauder hA hχ α hT uLim i) hBound
  refine ⟨W,K,by dsimp only [K]; positivity,hSch,
    (F05CanonicalJetFunction_continuousOn hA hχ α hT uLim).mono
      (prod_mono (subset_univ _) subset_rfl),
    F05CanonicalJetFunction_initial A χ α hT.le uLim,?_,?_⟩
  · intro x hx t ht
    exact F05CanonicalJetFunction_lateral hA hχ α hT.le uLim hx ht
  · intro i p
    have hEval := F05_compatible_jet_evaluation_tendsto A hT.le u uLim hu i p
    have hReal := F05CanonicalJetFunction_realizes hA hχ α hT uLim i
    have hValue := F05CanonicalJetFunction_value hA hχ α hT.le uLim i p.property.1 p.property.2
    have hGrad := hReal.2.1 p.property
    have hHess := hReal.2.2.1 p.property
    have hTime := hReal.2.2.2 p.property
    rw [F05BCFFun_apply _ p] at hValue hGrad hHess hTime
    change spatialD (pull A i W) p.val = (uLim.val i).val.2.1 p at hGrad
    change spatialDD (pull A i W) p.val = (uLim.val i).val.2.2.1.val.1 p at hHess
    change timeD (F05Q A i T) (pull A i W) p.val = (uLim.val i).val.2.2.2.val.1 p at hTime
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [← hValue,W,pull] using hEval.1
    · simpa only [← hGrad] using hEval.2.1
    · simpa only [← hHess] using hEval.2.2.1
    · simpa only [← hTime] using hEval.2.2.2

end Yau.Proofs.F05Aux

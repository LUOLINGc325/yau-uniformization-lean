import Yau.Proofs.C01ExitProfileContinuity
import Yau.Proofs.C01ExitExponentialComparison
import Yau.Proofs.C01CompletenessFromExit
import Yau.Proofs.C01ExitCrossing

/-! The genuine upper-support differential estimate implies sequence
completeness of the exact positive-time length distance. The geometric
construction of those supports is a separate input to this lemma. -/

noncomputable section
open scoped Topology Manifold ContDiff

namespace Yau.NodeProofs.C01Aux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_complete_of_exit_support
    (hflow : LocalizedFlow X o h U P ρ) (T C : ℝ) (hT : 0 ≤ T) (hC : 0 < C)
    (hpaths : ∀ L : ℝ, 0 < L → ∀ a ∈ Set.Ioc 0 T,
      ∃ (f : ℝ → ℝ) (d : ℝ),
        f a = exitDistanceProfile X.metric (h a) o L ∧
        (∀ u ∈ Set.Icc 0 T, exitDistanceProfile X.metric (h u) o L ≤ f u) ∧
        HasDerivAt f d a ∧
        -(C / Real.sqrt a) * (1 + exitDistanceProfile X.metric (h a) o L) ≤ d) :
    IsCompleteDistance (inducedDistance (h T)) := by
  have hk := localizedFlow_metricSmooth_nonneg hflow T hT
  apply complete_distance_of_exit_profile X.metric (h T) hk o
  · intro R
    let b := Real.exp (-2 * C * Real.sqrt T)
    have hb : 0 < b := Real.exp_pos _
    let L := max 1 ((R + 2) / b)
    have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hscaled : R + 2 ≤ L * b := (div_le_iff₀ hb).mp (le_max_right _ _)
    have hbarrier : R < (1 + L) * b - 1 := by nlinarith
    have hcontinuous : ContinuousOn (fun t => exitDistanceProfile X.metric (h t) o L)
        (Set.Icc 0 T) :=
      (localizedFlow_exit_profile_continuousOn hflow L hL).mono (fun _ ht => ht.1)
    have hzero : exitDistanceProfile X.metric (h 0) o L = L := by
      rw [hflow.1.1]
      exact exitDistanceProfile_initial X.metric o L hL.le
    have hlower := exit_profile_exponential_lower_bound
      (fun t => exitDistanceProfile X.metric (h t) o L) L C T hT hC hcontinuous hzero
      (hpaths L hL) T ⟨hT, le_rfl⟩
    exact ⟨L, hL.le, hbarrier.trans_le hlower⟩
  · exact fun L hL x hx => exitDistanceProfile_le_distance_outside X.metric (h T) hk o L hL x hx

end Yau.NodeProofs.C01Aux

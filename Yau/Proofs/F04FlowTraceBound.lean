import Yau.Proofs.F04SpaceTimeLaplacian
import Yau.Proofs.F04GradientTraceBound

open Filter Set
open scoped Topology ContDiff Manifold Matrix

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint Yau.LeafProofs.L18Aux

variable {n : ℕ}

theorem physical_heatOp_continuousOn
    (X : KahlerManifold n) (h : Flow X) {S : ℝ} (hS : 0 < S)
    (hh : MetricFamilySmooth h (Icc 0 S)) {Q : STF X}
    (hQ : SmoothSpaceTime Q (Icc 0 S)) :
    ContinuousOn (fun p : Pt X × ℝ => heatOp h (Icc 0 S) Q p.1 p.2)
      (univ ×ˢ Icc 0 S) :=
  (smoothSpaceTime_timeDerivativeWithin_continuousOn hS hQ).sub
    (smoothSpaceTime_continuousOn (metricFamily_laplacian_spaceTime_smooth h hS hh hQ))

/-- The supplied flow's own Q barrier bounds the intrinsic inverse-metric
 trace uniformly on every compact physical slab. -/
theorem flow_compact_trace_bound
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) {S : ℝ} (hS : 0 < S)
    (K : Set (Pt X)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ t ∈ Icc 0 S,
      traceWith (gMat (h t) x) (gMat X.metric.form x) ≤ C := by
  rcases hloc with ⟨hflow, _hU, _hP, _hρ, _hLE, _hmetric, _hinit,
    _hUder, _hPlog, _hρdata, _hPder, _hMass, _hGrowth, hBarrier⟩
  obtain ⟨Q, c, hc, hQ, hbar⟩ := hBarrier S hS
  have hh : MetricFamilySmooth h (Icc 0 S) := fun a i j =>
    (hflow.2.1 a i j).mono (prod_mono (Subset.refl _) (fun _ ht => ht.1))
  have hcont := physical_heatOp_continuousOn X h hS hh hQ
  obtain ⟨A, hA⟩ := (hK.prod isCompact_Icc).bddAbove_image
    (hcont.mono (prod_mono (subset_univ _) (Subset.refl _)))
  refine ⟨max (A / c) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x hx t ht
  have hb := ((hbar x t ht).2.2).trans (hA ⟨(x, t), ⟨hx, ht⟩, rfl⟩)
  exact ((le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hb)).trans (le_max_left _ _)

/-- One coefficient bound controls every supported smooth test simultaneously. -/
theorem flow_compact_gradient_comparison
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) {S : ℝ} (hS : 0 < S)
    (K : Set (Pt X)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Pt X → ℝ, SmoothFn f → ∀ x ∈ K, ∀ t ∈ Icc 0 S,
      scalarGradientPair X.metric.form f f x ≤ scalarGradientPair (h t) f f x ∧
      scalarGradientPair (h t) f f x ≤ C * scalarGradientPair X.metric.form f f x := by
  obtain ⟨C, hC, hCb⟩ := flow_compact_trace_bound X o h U P ρ hloc hS K hK
  refine ⟨C, hC, ?_⟩
  intro f hf x hx t ht
  exact ⟨flow_scalarGradientPair_lower_bound X o h U P ρ hloc ht.1 f x,
    (scalarGradientPair_le_trace (h t) X.metric.form hf x).trans
      (mul_le_mul_of_nonneg_right (hCb x hx t ht)
        (scalarGradientPair_self_nonneg X.metric.form f x))⟩

end Yau.F04Proof

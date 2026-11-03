import Yau.Proofs.F04ClosedSpatialDerivative
import Yau.Proofs.F04ChartCoefficients
import Yau.Proofs.F04CompactLpProfiles

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint Yau.LeafProofs.L18Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- Physical scalar gradient pairings vary continuously for the actual
 evolving Hermitian family, including both closed time faces. -/
theorem metricFamily_gradientPair_continuousOn
    (h : ℝ → HermitianField M) {S : ℝ} (hS : 0 < S)
    (hh : MetricFamilySmooth h (Icc 0 S))
    {u v : M.Carrier → ℝ → ℝ} (hu : SmoothSpaceTime u (Icc 0 S))
    (hv : SmoothSpaceTime v (Icc 0 S)) :
    ContinuousOn (fun p : M.Carrier × ℝ =>
      scalarGradientPair (h p.2) (fun x => u x p.2) (fun x => v x p.2) p.1)
        (univ ×ˢ Icc 0 S) := by
  apply chartwise_continuousOn (M := M) (I := Icc 0 S)
    (v := fun x t => scalarGradientPair (h t) (fun y => u y t) (fun y => v y t) x)
  intro c
  have hi (i j : RIdx n) : ContinuousOn (fun p : ComplexVector n × ℝ =>
      (realMetricFn (h p.2) c p.1)⁻¹ i j) (chartTarget c ×ˢ Icc 0 S) :=
    (contDiffOn_matrix_inv (hh c)
      (fun p hp => (Yau.LeafProofs.L12Aux.realMetricFn_posDef (h p.2) c p.1 hp.1).det_pos.ne') i j).continuousOn
  have hsum : ContinuousOn (fun p : ComplexVector n × ℝ => ∑ i, ∑ j,
      (realMetricFn (h p.2) c p.1)⁻¹ i j * rDeriv (inChart c (fun x => u x p.2)) p.1 i *
        rDeriv (inChart c (fun x => v x p.2)) p.1 j) (chartTarget c ×ˢ Icc 0 S) := by
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    exact ((hi i j).mul (chart_spatial_derivative_continuousOn hS hu c i)).mul
      (chart_spatial_derivative_continuousOn hS hv c j)
  apply hsum.congr
  intro p hp
  have hus : SmoothFn (fun x => u x p.2) := fun a => (hu a).comp
    (contDiffOn_id.prodMk contDiffOn_const) (fun _ hz => ⟨hz, hp.2⟩)
  have hvs : SmoothFn (fun x => v x p.2) := fun a => (hv a).comp
    (contDiffOn_id.prodMk contDiffOn_const) (fun _ hz => ⟨hz, hp.2⟩)
  dsimp only
  rw [scalarGradientPair_eq_chart (h p.2) hus hvs c hp.1, chartGradientPair_eq_sum]

theorem flow_rho_gradient_bound
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) {S : ℝ} (hS : 0 < S)
    (K : Set (Pt X)) (hK : IsCompact K) :
    ∃ D : ℝ, 0 < D ∧ ∀ x ∈ K, ∀ t ∈ Icc 0 S,
      scalarGradientPair (h t) (fun y => ρ y t) (fun y => ρ y t) x ≤ D := by
  have hh : MetricFamilySmooth h (Icc 0 S) := fun c i j =>
    (hloc.1.2.1 c i j).mono (prod_mono (Subset.refl _) (fun _ ht => ht.1))
  have hρ : SmoothSpaceTime ρ (Icc 0 S) := fun c => (hloc.2.2.2.1 c).mono
    (prod_mono (Subset.refl _) (fun _ ht => ht.1))
  have hc := metricFamily_gradientPair_continuousOn h hS hh hρ hρ
  obtain ⟨C, hCb⟩ := (hK.prod isCompact_Icc).bddAbove_image
    (hc.mono (prod_mono (subset_univ _) (Subset.refl _)))
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x hx t ht
  exact (hCb ⟨(x, t), ⟨hx, ht⟩, rfl⟩).trans (le_max_left _ _)

end Yau.F04Proof

import Yau.Proofs.F01ChartMetricOrder
import Yau.Proofs.F01RelativeScalarSandwich
import Yau.Proofs.F01ChartGramSmooth
import Yau.Proofs.F01MatrixSandwichMono
import Yau.Proofs.F01BoundedGeometryComplete

/-! Actual uniform native chart-jet bounds and metric comparison on the
original bounded-geometry atlas produce the precise bounded geometry and
induced-distance completeness needed to restart the original short-time solver. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem restart_geometry_from_actual_chart_jets
    (α k : HermitianField M) (hk : MetricSmooth k) (A : BoundedChartFamily α)
    {C : ℝ} (hC : 0 < C)
    (hrelative : ∀ x,
      (gMat k x - ((C⁻¹ : ℝ) : ℂ) • gMat α x).PosSemidef ∧
      ((C : ℂ) • gMat α x - gMat k x).PosSemidef)
    (B : ℕ → ℝ)
    (hjets : ∀ p q z, z ∈ ball (0 : ComplexVector n) A.radius → ∀ i j,
      ‖iteratedFDeriv ℝ q (fun w => pullbackMatrix k (A.chart p) w i j) z‖ ≤ B q) :
    Yau.LeafCandidates.HermitianBoundedGeometry k ∧ IsCompleteDistance (inducedDistance k) := by
  let D := C * A.bound 0
  let E : ℕ → ℝ := fun q => max (D + 1) (|B q| + 1)
  have hD : 0 < D := mul_pos hC (A.bound_pos 0)
  have hE (q : ℕ) : 0 < E q := by
    exact (show 0 < |B q| + 1 by positivity).trans_le (le_max_right _ _)
  have hDE : D ≤ E 0 := (le_add_of_nonneg_right zero_le_one).trans (le_max_left _ _)
  have hBG : Yau.LeafCandidates.HermitianBoundedGeometry k := by
    refine ⟨A.radius, A.radius_pos, E, hE, ?_⟩
    intro p
    refine ⟨A.chart p, A.center p, A.closedBall_source p, A.differentiable p,
      A.inverse_differentiable p, ?_, ?_, ?_⟩
    · intro z hz
      have ha := A.comparison p z hz
      have hal : (pullbackMatrix α (A.chart p) z - (((A.bound 0)⁻¹ : ℝ) : ℂ) • 1).PosSemidef := by
        simpa only [Complex.ofReal_inv] using ha.1
      have hlocal := relative_scalar_matrix_sandwich
        (H := pullbackMatrix α (A.chart p) z) (K := pullbackMatrix k (A.chart p) z)
        (ell := (A.bound 0)⁻¹) (upper := A.bound 0) (c := C⁻¹) (C := C)
        (inv_nonneg.mpr hC.le) hC.le hal ha.2
        (metric_lower_order_in_chart α k (A.chart p) z (hrelative (A.chart p z)).1)
        (metric_upper_order_in_chart α k (A.chart p) z (hrelative (A.chart p z)).2)
      have he : C⁻¹ * (A.bound 0)⁻¹ = D⁻¹ := by dsimp only [D]; rw [mul_inv_rev]; ring
      rw [he] at hlocal
      change (pullbackMatrix k (A.chart p) z - (E 0 : ℂ)⁻¹ • 1).PosSemidef ∧
        ((E 0 : ℂ) • 1 - pullbackMatrix k (A.chart p) z).PosSemidef
      simpa only [Complex.ofReal_inv] using matrix_sandwich_mono hD (hE 0) hDE hlocal
    · intro i j
      exact (pullbackMatrix_entry_contDiffOn k hk (A.chart p) (A.differentiable p) i j).mono
        (ball_subset_closedBall.trans (A.closedBall_source p))
    · intro q z hz i j
      exact (hjets p q z hz i j).trans ((le_abs_self (B q)).trans
        ((le_add_of_nonneg_right zero_le_one).trans (le_max_right _ _)))
  exact ⟨hBG, completeDistance_of_hermitianBoundedGeometry k hk hBG⟩

end Yau.NodeProofs.F01Aux

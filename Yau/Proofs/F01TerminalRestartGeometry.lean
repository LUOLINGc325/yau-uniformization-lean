import Yau.Proofs.F01SmoothHermitianChartLimit
import Yau.Proofs.F01InverseTensorDilation
import Yau.Proofs.F01PhysicalNativeChartJets

/-! Bounds on actual convergent rescaled jets pass to the constructed
terminal metric and recover all original-chart coefficient bounds.
The resulting restart geometry and completeness are properties of
that same terminal field. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Manifold Topology Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem restart_geometry_of_actual_chart_jet_limits
    (g K : HermitianField M) (hg : MetricSmooth g) (hK : MetricSmooth K)
    (A : BoundedChartFamily g) (k : ℕ → HermitianField M)
    {σ C : ℝ} (hσ : 0 < σ) (hσr : σ ≤ A.radius) (hC : 0 < C)
    (hOrders : ∀ x, (gMat K x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
      ((C : ℂ) • gMat g x - gMat K x).PosSemidef)
    (B : ℕ → ℝ)
    (hBounds : ∀ a q m x, x ∈ ball 0 (1 / 2) →
      ‖iteratedFDeriv ℝ q (fun z => pullbackMatrix (k m) (A.chart a) (σ • z)) x‖ ≤ B q)
    (hJets : ∀ a q, TendstoUniformlyOn
      (fun m x => iteratedFDeriv ℝ q (fun z => pullbackMatrix (k m) (A.chart a) (σ • z)) x)
      (iteratedFDeriv ℝ q (fun z => pullbackMatrix K (A.chart a) (σ • z)))
      atTop (ball 0 (1 / 2))) :
    Yau.LeafCandidates.HermitianBoundedGeometry K ∧ IsCompleteDistance (inducedDistance K) := by
  classical
  have hLimitBound (a : M.Carrier) (q : ℕ) (x : Space n) (hx : x ∈ ball 0 (1 / 2)) :
      ‖iteratedFDeriv ℝ q (fun z => pullbackMatrix K (A.chart a) (σ • z)) x‖ ≤ B q :=
    le_of_tendsto ((hJets a q).tendsto_at hx).norm
      (Eventually.of_forall (fun m => hBounds a q m x hx))
  have each := fun q : ℕ => inverse_spatial_jet_budget (E := Space n)
    (F := Matrix (Fin n) (Fin n) ℂ) q hσ.ne'
  choose I hI hInverse using each
  obtain ⟨E, hE, hEntry⟩ := frobenius_entry_common_budget n
  apply restart_geometry_on_actual_smaller_charts g K hK A
    (r := σ / 2) (C := C) (by positivity) (by linarith) hC hOrders
    (fun q => E * (I q * B q))
  intro a q z hz i j
  let f := fun w => pullbackMatrix K (A.chart a) w
  have hf : ContDiffOn ℝ ∞ f (ball 0 A.radius) :=
    matrix_contDiffOn_of_entries (fun i j =>
      (pullbackMatrix_entry_contDiffOn K hK (A.chart a) (A.differentiable a) i j).mono
        (ball_subset_closedBall.trans (A.closedBall_source a)))
  let x := σ⁻¹ • z
  have hx : x ∈ ball 0 (1 / 2) := by
    rw [mem_ball, dist_zero_right]
    change ‖σ⁻¹ • z‖ < 1 / 2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hσ)]
    have hzN : ‖z‖ < σ / 2 := by simpa only [mem_ball, dist_zero_right] using hz
    calc
      _ < σ⁻¹ * (σ / 2) := mul_lt_mul_of_pos_left hzN (inv_pos.mpr hσ)
      _ = 1 / 2 := by field_simp [hσ.ne']
  have hσx : σ • x = z := by dsimp only [x]; rw [smul_smul, mul_inv_cancel₀ hσ.ne', one_smul]
  have hxOld : σ • x ∈ ball 0 A.radius :=
    spatialDilation_mem_ball hσ hσr (ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1) hx)
  have hzOld : z ∈ ball 0 A.radius := by simpa only [hσx] using hxOld
  have hPhysical := hInverse q (ball 0 A.radius) f x (B q) isOpen_ball hf hxOld (hLimitBound a q x hx)
  rw [hσx] at hPhysical
  exact (frobenius_entry_iteratedFDeriv_norm_le isOpen_ball hf hzOld q i j).trans
    (mul_le_mul (hEntry i j) hPhysical (norm_nonneg _) hE.le)

end Yau.NodeProofs.F01Aux

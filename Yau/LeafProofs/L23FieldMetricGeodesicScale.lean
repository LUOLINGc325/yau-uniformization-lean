import Yau.LeafProofs.L23FieldMetricGeodesicSplice

/-! Real affine speed normalization preserves the actual all-chart geodesic equation. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}

theorem geoChartState_mul (γ : ℝ → M.Carrier) (c : M.Carrier) (k t : ℝ) :
    geoChartState (fun u => γ (k*u)) c t =
      ((geoChartState γ c (k*t)).1,k • (geoChartState γ c (k*t)).2) := by
  apply Prod.ext
  · rfl
  · exact deriv_comp_mul_left k (fun u => chartPt c (γ u)) t

theorem fieldGeodesicOn_mul (h : HermitianField M) (γ : ℝ → M.Carrier)
    (J : Set ℝ) (hγ : FieldGeodesicOn h γ J) (k : ℝ) :
    FieldGeodesicOn h (fun u => γ (k*u)) {u : ℝ | k*u ∈ J} := by
  letI := manifold_realSmooth M
  have hmul : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 3 (fun u : ℝ => k*u) :=
    (contDiff_const.mul contDiff_id).contMDiff
  refine ⟨hγ.1.comp hmul.contMDiffOn (fun u hu => hu),?_⟩
  intro c t ht hc
  let φ : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n × ComplexVector n :=
    fun _ u => geoChartState γ c u
  have H := normalizedChartFlow_hasDerivAt h c k φ (0,0) t (hγ.2 c (k*t) ht hc)
  have hEq : geoChartState (fun u => γ (k*u)) c = normalizedChartFlow k φ (0,0) := by
    funext u
    exact geoChartState_mul γ c k u
  rw [hEq]
  exact H

end Yau.LeafProofs.L23Aux

import Yau.LeafProofs.L23FieldMetricGeodesicGluing
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Time translation preserves the actual all-chart geodesic equation. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}

theorem geoChartState_shift (γ : ℝ → M.Carrier) (c : M.Carrier) (a t : ℝ) :
    geoChartState (fun u => γ (u-a)) c t = geoChartState γ c (t-a) := by
  apply Prod.ext
  · rfl
  · exact deriv_comp_sub_const (fun u => chartPt c (γ u)) a t

theorem fieldGeodesicOn_shift (h : HermitianField M) (γ : ℝ → M.Carrier)
    (J : Set ℝ) (hγ : FieldGeodesicOn h γ J) (a : ℝ) :
    FieldGeodesicOn h (fun u => γ (u-a)) {u : ℝ | u-a ∈ J} := by
  letI := manifold_realSmooth M
  have hshift : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 3 (fun u : ℝ => u-a) :=
    (contDiff_id.sub contDiff_const).contMDiff
  refine ⟨hγ.1.comp hshift.contMDiffOn (fun u hu => hu),?_⟩
  intro c t ht hc
  have H := HasDerivAt.comp_sub_const t a (hγ.2 c (t-a) ht hc)
  have hEq : geoChartState (fun u => γ (u-a)) c = (fun u => geoChartState γ c (u-a)) := by
    funext u
    exact geoChartState_shift γ c a u
  rw [hEq]
  simpa only [one_smul,Function.comp_def] using H

end Yau.LeafProofs.L23Aux

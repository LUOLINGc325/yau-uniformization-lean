import Yau.Proofs.C01IndexCutoffJets

/-! The actual first and second radial jets of a parallel-endpoint
variation scale to the prescribed smooth endpoint cutoff. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.NodeProofs.C01Aux

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem indexWeighted_radial_first
    (F : V → W) (P : V →L[ℝ] W) (κ u : ℝ) (hκ : 0 < κ) (w : V)
    (hfirst : ∀ v : V, HasDerivAt (fun r : ℝ => F (r • v)) (u • P v) 0) :
    HasDerivAt (fun r : ℝ => F (indexCutoffRatio κ u • (r • w)))
      (indexCutoff κ u • P w) 0 := by
  have heq : (fun r : ℝ => F (indexCutoffRatio κ u • (r • w))) =
      (fun r : ℝ => F (r • (indexCutoffRatio κ u • w))) := by
    funext r
    simp only [smul_smul, mul_comm (indexCutoffRatio κ u) r]
  rw [heq]
  have H := hfirst (indexCutoffRatio κ u • w)
  simpa only [map_smul, smul_smul, indexCutoffRatio_mul hκ u] using H

theorem indexWeighted_radial_second
    (F : V → W) (P : V →L[ℝ] W) (Γ : W →L[ℝ] W →L[ℝ] W)
    (κ u : ℝ) (hκ : 0 < κ) (w : V)
    (hsecond : ∀ v : V, HasDerivAt (deriv (fun r : ℝ => F (r • v)))
      (-Γ (u • P v) (u • P v)) 0) :
    HasDerivAt (deriv (fun r : ℝ => F (indexCutoffRatio κ u • (r • w))))
      (-Γ (indexCutoff κ u • P w) (indexCutoff κ u • P w)) 0 := by
  have heq : (fun r : ℝ => F (indexCutoffRatio κ u • (r • w))) =
      (fun r : ℝ => F (r • (indexCutoffRatio κ u • w))) := by
    funext r
    simp only [smul_smul, mul_comm (indexCutoffRatio κ u) r]
  rw [heq]
  have H := hsecond (indexCutoffRatio κ u • w)
  simpa only [map_smul, smul_smul, indexCutoffRatio_mul hκ u] using H

theorem scalar_parallel_field_hasDerivAt
    (Γ : W →L[ℝ] W →L[ℝ] W) (T : W) (P : ℝ → W) (φ : ℝ → ℝ)
    (u c : ℝ) (hP : HasDerivAt P (-Γ T (P u)) u) (hφ : HasDerivAt φ c u) :
    HasDerivAt (fun s => φ s • P s)
      (c • P u - Γ T (φ u • P u)) u := by
  have H := hφ.smul hP
  convert H using 1
  simp only [map_smul, smul_neg, sub_eq_add_neg, add_comm]

end Yau.NodeProofs.C01Aux

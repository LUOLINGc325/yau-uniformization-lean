import Yau.Proofs.P04CutoffAnnulus
import Yau.Proofs.P04PoleAnnulusBounds

noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

/-- The full closed support of the ACTUAL dbar source lies in the original
chart and in the fixed compact model annulus. -/
theorem cutoffDbar_support_in_annulus (p : M.Carrier) {χ : ComplexVector n → ℝ}
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ chartTarget p) {ρ : ℝ} (hρ : 0 < ρ)
    (hsupp : tsupport χ ⊆ Metric.closedBall (chartPt p p) (3*ρ/2))
    (hone : ∀ z ∈ Metric.closedBall (chartPt p p) ρ, χ z=1) :
    ∀ x ∈ closure {y | cutoffDbar p χ y ≠ (0 : BundleDbar.NQForm (CanonicalCoefficients M) 1) y},
      x ∈ (extChartAt (ComplexModel n) p).source ∧ chartPt p x ∈ poleAnnulus (chartPt p p) ρ := by
  let F := cutoffCoefficient χ
  have hcF : HasCompactSupport F := cutoffCoefficient_compact hc
  have hsD : tsupport (L14Aux.modelTopDbar F) ⊆ BundleDbar.localDomain (r := 1) (CanonicalCoefficients M) p := by
    rw [coefficient_localDomain]
    exact (L14Aux.tsupport_modelTopDbar_subset F).trans (cutoffCoefficient_tsupport.trans hs)
  have hcD : HasCompactSupport (L14Aux.modelTopDbar F) :=
    hcF.of_isClosed_subset (isClosed_tsupport _) (L14Aux.tsupport_modelTopDbar_subset F)
  have himage := L14Aux.oneFormPushforward_support (CanonicalCoefficients M) p
    (L14Aux.modelTopDbar F) hcD hsD
  let O : Set M.Carrier := (extChartAt (ComplexModel n) p).source ∩
    (chartPt p) ⁻¹' Metric.ball (chartPt p p) ρ
  have hO : IsOpen O := (continuousOn_extChartAt (I := ComplexModel n) p).isOpen_inter_preimage
    (isOpen_extChartAt_source p) Metric.isOpen_ball
  have hsub : {y | cutoffDbar p χ y ≠ (0 : BundleDbar.NQForm (CanonicalCoefficients M) 1) y} ⊆ Oᶜ := by
    intro y hy hyO
    exact hy (oneFormPushforward_zero_at p y _ (cutoff_model_zero_inner hone hyO.2))
  intro x hx
  obtain ⟨z,hz,rfl⟩ := himage hx
  have hzχ : z ∈ tsupport χ :=
    cutoffCoefficient_tsupport ((L14Aux.tsupport_modelTopDbar_subset F) hz)
  have hzt : z ∈ chartTarget p := hs hzχ
  have hi : chartPt p (chartInv p z)=z := (extChartAt (ComplexModel n) p).right_inv hzt
  have hxsource := (extChartAt (ComplexModel n) p).map_target hzt
  refine ⟨hxsource,?_⟩
  rw [hi]
  refine ⟨Metric.closedBall_subset_closedBall (by linarith : 3*ρ/2 ≤ 2*ρ) (hsupp hzχ),?_⟩
  intro hinner
  have hρinner : z ∈ Metric.ball (chartPt p p) ρ :=
    Metric.ball_subset_ball (by linarith : ρ/2 ≤ ρ) hinner
  apply closure_minimal hsub hO.isClosed_compl hx
  exact ⟨hxsource,by change chartPt p (chartInv p z) ∈ Metric.ball (chartPt p p) ρ; rwa [hi]⟩

end Yau.Proofs.P04Aux

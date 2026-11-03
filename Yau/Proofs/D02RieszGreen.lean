import Yau.LeafProofs.L08
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section
namespace Yau.NodeProofs.D02RieszAux

/-- A locally continuous factor may be multiplied by an interior compact test
without imposing any regularity on its values outside the domain. -/
theorem integrable_mul_compact {f g : ℂ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : ContinuousOn g (tsupport f)) : Integrable (fun z ↦ g z * f z) volume := by
  apply (hg.mul hf.continuousOn).integrableOn_compact hfc
    |>.integrable_of_forall_notMem_eq_zero
  intro z hz
  change g z * f z = 0
  rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]

/-- Green's identity for one fixed real direction, with regularity of the
potential required only on the open domain. -/
theorem integral_second_direction {U : Set ℂ} (hU : IsOpen U)
    {u φ : ℂ → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (a : ℂ) :
    (∫ z, u z * fderiv ℝ (fun w ↦ fderiv ℝ φ w a) z a) =
      ∫ z, fderiv ℝ (fun w ↦ fderiv ℝ u w a) z a * φ z := by
  let du := fun z ↦ fderiv ℝ u z a
  let dφ := fun z ↦ fderiv ℝ φ z a
  have hdu : ContDiffOn ℝ ∞ du U :=
    (hu.fderiv_of_isOpen (m := ∞) hU (by simp)).clm_apply contDiffOn_const
  have hdφ : ContDiff ℝ ∞ dφ := (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hddφ : ContDiff ℝ ∞ (fun z ↦ fderiv ℝ dφ z a) :=
    (hdφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hdφc : HasCompactSupport dφ := hφc.fderiv_apply ℝ a
  have hddφc : HasCompactSupport (fun z ↦ fderiv ℝ dφ z a) := hdφc.fderiv_apply ℝ a
  have hdφU : tsupport dφ ⊆ U := (tsupport_fderiv_apply_subset ℝ a).trans hφU
  have hddφU : tsupport (fun z ↦ fderiv ℝ dφ z a) ⊆ U :=
    (tsupport_fderiv_apply_subset ℝ a).trans hdφU
  have hddU : ContinuousOn (fun z ↦ fderiv ℝ du z a) U :=
    ((hdu.fderiv_of_isOpen (m := ∞) hU (by simp)).clm_apply contDiffOn_const).continuousOn
  have h1 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := u) (g := dφ) (v := a)
    (integrable_mul_compact hdφ.continuous hdφc (hdu.continuousOn.mono hdφU))
    (integrable_mul_compact hddφ.continuous hddφc (hu.continuousOn.mono hddφU))
    (integrable_mul_compact hdφ.continuous hdφc (hu.continuousOn.mono hdφU))
    (fun z hz ↦ (hu.contDiffAt (hU.mem_nhds (hdφU hz))).differentiableAt (by simp))
    (fun z _ ↦ hdφ.differentiable (by simp) z)
  have h2 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := du) (g := φ) (v := a)
    (integrable_mul_compact hφ.continuous hφc (hddU.mono hφU))
    (integrable_mul_compact hdφ.continuous hdφc (hdu.continuousOn.mono hdφU))
    (integrable_mul_compact hφ.continuous hφc (hdu.continuousOn.mono hφU))
    (fun z hz ↦ (hdu.contDiffAt (hU.mem_nhds (hφU hz))).differentiableAt (by simp))
    (fun z _ ↦ hφ.differentiable (by simp) z)
  change (∫ z, u z * fderiv ℝ dφ z a) = ∫ z, fderiv ℝ du z a * φ z
  exact h1.trans (by rw [h2, neg_neg])

/-- The frozen real planar Laplacian is self-adjoint on interior smooth tests. -/
theorem integral_laplacian_swap {U : Set ℂ} (hU : IsOpen U)
    {u φ : ℂ → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    (∫ z, u z * LeafCandidates.realPlanarLaplacian φ z) =
      ∫ z, LeafCandidates.realPlanarLaplacian u z * φ z := by
  have hdir (a : ℂ) : Integrable
      (fun z ↦ u z * fderiv ℝ (fun w ↦ fderiv ℝ φ w a) z a) volume := by
    apply integrable_mul_compact
      ((((hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).fderiv_right (m := ∞) (by simp)).clm_apply
        contDiff_const).continuous ((hφc.fderiv_apply ℝ a).fderiv_apply ℝ a)
    exact hu.continuousOn.mono
      (((tsupport_fderiv_apply_subset ℝ a).trans (tsupport_fderiv_apply_subset ℝ a)).trans hφU)
  have hdu (a : ℂ) : Integrable
      (fun z ↦ fderiv ℝ (fun w ↦ fderiv ℝ u w a) z a * φ z) volume := by
    apply integrable_mul_compact hφ.continuous hφc
    have hd : ContDiffOn ℝ ∞ (fun z ↦ fderiv ℝ u z a) U :=
      (hu.fderiv_of_isOpen (m := ∞) hU (by simp)).clm_apply contDiffOn_const
    have hdd : ContDiffOn ℝ ∞ (fun z ↦ fderiv ℝ (fun w ↦ fderiv ℝ u w a) z a) U :=
      (hd.fderiv_of_isOpen (m := ∞) hU (by simp)).clm_apply contDiffOn_const
    exact hdd.continuousOn.mono hφU
  calc
    _ = ∫ z, u z * fderiv ℝ (fun w ↦ fderiv ℝ φ w 1) z 1 +
        u z * fderiv ℝ (fun w ↦ fderiv ℝ φ w Complex.I) z Complex.I := by
      congr 1; funext z
      rw [LeafProofs.L08_realPlanarLaplacian_eq_directions (hφ.contDiffAt.of_le (by simp)), mul_add]
    _ = (∫ z, fderiv ℝ (fun w ↦ fderiv ℝ u w 1) z 1 * φ z) +
        ∫ z, fderiv ℝ (fun w ↦ fderiv ℝ u w Complex.I) z Complex.I * φ z := by
      rw [integral_add (hdir 1) (hdir Complex.I),
        integral_second_direction hU hu hφ hφc hφU 1,
        integral_second_direction hU hu hφ hφc hφU Complex.I]
    _ = ∫ z, LeafCandidates.realPlanarLaplacian u z * φ z := by
      rw [← integral_add (hdu 1) (hdu Complex.I)]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro z
      dsimp only
      by_cases hz : z ∈ tsupport φ
      · rw [LeafProofs.L08_realPlanarLaplacian_eq_directions
          ((hu.contDiffAt (hU.mem_nhds (hφU hz))).of_le (by simp)), add_mul]
      · rw [image_eq_zero_of_notMem_tsupport hz]; simp

end Yau.NodeProofs.D02RieszAux

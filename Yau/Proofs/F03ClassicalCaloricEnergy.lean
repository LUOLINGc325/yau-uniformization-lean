import Yau.Proofs.F03DirectionalJets
import Yau.LeafProofs.L16EnergyEquation

/-! Actual weak gradients and local energy of every locally smooth scalar field. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates LeafProofs.L16Aux LeafProofs.L18Aux
variable {d : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

def classicalCaloricGradient (v : Point d → ℝ) (p : Point d) (i : RIdx d) : ℝ :=
  fderiv ℝ v p (realVec i,0)

theorem local_smooth_test_directional_ibp {Q : Set (Point d)} (hQ : IsOpen Q)
    {v φ : Point d → ℝ} (hv : ContDiffOn ℝ ∞ v Q) (hφ : Test Q φ) (e : Point d) :
    (∫ p, v p*fderiv ℝ φ p e ∂volume.restrict Q)=
      -(∫ p, fderiv ℝ v p e*φ p ∂volume.restrict Q) := by
  rw [integral_mul_test_eq (test_directionalDerivative hφ e) v,
    integral_mul_test_eq hφ (fun p => fderiv ℝ v p e)]
  have h := integral_compactTest_direction_on (volume : Measure (Point d)) hQ
    (hφ.1.of_le (by simp)) hφ.2.1 hφ.2.2 (hv.of_le (by simp)) e
  have hl : (∫ p, φ p*fderiv ℝ v p e)=(∫ p, fderiv ℝ v p e*φ p) := by
    apply integral_congr_ae
    exact ae_of_all _ (fun p => mul_comm _ _)
  have hr : (∫ p, fderiv ℝ φ p e*v p)=(∫ p, v p*fderiv ℝ φ p e) := by
    apply integral_congr_ae
    exact ae_of_all _ (fun p => mul_comm _ _)
  rw [hl,hr] at h
  linarith only [h]

theorem classicalCaloricGradient_weakGradient (O : Set (Space d)) (I : Set ℝ)
    (hD : IsOpen (O ×ˢ I)) (v : Point d → ℝ) (hv : ContDiffOn ℝ ∞ v (O ×ˢ I)) :
    WeakGradient O I v (classicalCaloricGradient v) := by
  intro φ hφ i
  rw [productVolume_eq_restrict]
  have hφd : (fun p : Point d => Parabolic.d (fun x => φ (x,p.2)) p.1 i)=
      (fun p => fderiv ℝ φ p (realVec i,0)) := by
    funext p
    exact d_eq_joint_fderiv (hφ.1.differentiable (by simp) p) i
  have h := local_smooth_test_directional_ibp hD hv hφ (realVec i,0)
  calc
    _ = ∫ p, v p*fderiv ℝ φ p (realVec i,0) ∂volume.restrict (O ×ˢ I) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun p => congrArg (fun z : ℝ => v p*z) (congrFun hφd p))
    _ = _ := h

theorem continuousOn_memLp_two_of_isCompact {K : Set (Point d)} (hK : IsCompact K)
    {v : Point d → ℝ} (hv : ContinuousOn v K) : MemLp v 2 (volume.restrict K) := by
  letI : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top (μ := volume)⟩
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hv
  apply MemLp.of_bound (hv.aestronglyMeasurable hK.measurableSet) C
  filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
  exact hC p hp

theorem classicalCaloricGradient_localEnergy (O : Set (Space d)) (I : Set ℝ)
    (hD : IsOpen (O ×ˢ I)) (v : Point d → ℝ) (hv : ContDiffOn ℝ ∞ v (O ×ˢ I)) :
    LocalEnergy O I v (classicalCaloricGradient v) := by
  refine ⟨classicalCaloricGradient_weakGradient O I hD v hv,?_⟩
  intro V c r _hV hVc hVO hI
  have hKc : IsCompact (closure V ×ˢ Icc c r) := hVc.prod isCompact_Icc
  have hKD : closure V ×ˢ Icc c r ⊆ O ×ˢ I := fun p hp => ⟨hVO hp.1,hI hp.2⟩
  have hsmall : V ×ˢ Ioo c r ⊆ closure V ×ˢ Icc c r :=
    fun p hp => ⟨subset_closure hp.1,⟨hp.2.1.le,hp.2.2.le⟩⟩
  rw [productVolume_eq_restrict]
  refine ⟨(continuousOn_memLp_two_of_isCompact hKc (hv.continuousOn.mono hKD)).mono_measure
    (Measure.restrict_mono hsmall le_rfl),?_⟩
  intro i
  have hGi : ContDiffOn ℝ ∞ (fun p => classicalCaloricGradient v p i) (O ×ˢ I) :=
    (hv.fderiv_of_isOpen hD (by simp)).clm_apply contDiffOn_const
  exact (continuousOn_memLp_two_of_isCompact hKc (hGi.continuousOn.mono hKD)).mono_measure
    (Measure.restrict_mono hsmall le_rfl)

end Yau.Proofs.F03Aux

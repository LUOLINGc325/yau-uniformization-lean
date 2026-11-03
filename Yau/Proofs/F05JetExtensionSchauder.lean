import Yau.Proofs.F05JetCutoffPhysicalHolder

/-! The explicit local extension has a genuine Schauder bound with a fixed
constant before the time slab and the physical FTC jet are chosen. -/

open Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_local_extension_schauder_budget (A : AtlasData M) (i : Fin A.count)
    (φ : Space n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hSupport : tsupport φ ⊆ Metric.closedBall 0 (1/4))
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ E : ℝ, 0 < E ∧ ∀ (T : ℝ) (hT : 0 < T) (u : F05LocalFTCGraph A i α hT.le),
      SchauderBound α (cylinder univ 0 T) (F05LocalJetExtension A i φ u.val) (E*‖u.val‖) := by
  have hc : HasCompactSupport φ :=
    (isCompact_closedBall (0 : Space n) (1/4)).of_isClosed_subset (isClosed_tsupport φ) hSupport
  have hSupport₁ : tsupport φ ⊆ Metric.closedBall 0 1 :=
    hSupport.trans (Metric.closedBall_subset_closedBall (by norm_num))
  obtain ⟨R,hR,hRaw⟩ := F05_cutoff_jet_raw_bound φ hφ hc
  obtain ⟨H,hH,hHigh⟩ := F05_local_cutoff_high_budget A i φ hφ hSupport
  obtain ⟨N,hN,hNative⟩ := halfSpaceSecondOrderExtension_schauder hα hα1
  let E := R+H+N*(R+H)
  have hE : 0 < E := by dsimp only [E]; positivity
  have hRE : R ≤ E := by dsimp only [E]; nlinarith [mul_nonneg hN.le (add_nonneg hR.le hH.le)]
  have hHE : H ≤ E := by dsimp only [E]; nlinarith [mul_nonneg hN.le (add_nonneg hR.le hH.le)]
  have hNE : N*(R+H) ≤ E := by dsimp only [E]; linarith
  refine ⟨E,hE,?_⟩
  intro T hT u
  have hNorm := norm_nonneg u.val
  have hScaleR : R*‖u.val‖ ≤ E*‖u.val‖ := mul_le_mul_of_nonneg_right hRE hNorm
  have hScaleH : H*‖u.val‖ ≤ E*‖u.val‖ := mul_le_mul_of_nonneg_right hHE hNorm
  have hRawU := hRaw α (F05Q A i T) u.val
  have hHighU := hHigh α hα hα1 T hT u
  cases hν : A.normal i with
  | none =>
    have hOpen := F05ModelOpen_none A i hν
    have hJets := F05_local_extension_jets A i α hT u φ hφ hSupport₁
    rw [hOpen,closure_univ] at hJets hHighU
    have hHighH := holderBound_congr_on hHighU.1 (fun p hp => (hJets.2.2.2.1 hp).symm)
    have hHighT := holderBound_congr_on hHighU.2 (fun p hp => (hJets.2.2.2.2 hp).symm)
    refine ⟨hJets.1,mul_nonneg hE.le hNorm,?_,
      holderBound_mono_const hHighH hScaleH,holderBound_mono_const hHighT hScaleH⟩
    intro p hp
    rw [hJets.2.1 hp,hJets.2.2.1 hp]
    exact ⟨(hRawU p).1.trans hScaleR,(hRawU p).2.1.trans hScaleR⟩
  | some j =>
    have hOpen := F05ModelOpen_some A i hν
    have hClosed := F05ModelClosed_some A i hν
    have hCont := F05_cutoff_jet_continuousOn A i α T φ hφ hSupport₁ u.val
    have hSpace (p : Point n) :=
      F05_cutoff_jet_derivatives_model A i α hT.le u φ hφ hSupport₁ (p := p)
    have hTime (p : Point n) := F05_cutoff_jet_time_model A i α hT.le u φ hSupport₁ (p := p)
    rw [hClosed] at hCont hTime hHighU
    rw [hOpen] at hSpace
    have hKR : R*‖u.val‖ ≤ (R+H)*‖u.val‖ := by nlinarith
    have hKH : H*‖u.val‖ ≤ (R+H)*‖u.val‖ := by nlinarith
    have hSchauder := hNative (-realVec j) T
      (F05CutoffJetValue φ u.val) (F05CutoffJetGradient φ u.val)
      (F05CutoffJetHessian φ u.val) (F05CutoffJetTime φ u.val) ((R+H)*‖u.val‖)
      (by simp only [norm_neg,realVec_norm]) hT
      hCont.1 hCont.2.1 hCont.2.2.1 hCont.2.2.2
      (fun p hp => (hSpace p hp).1) (fun p hp => (hSpace p hp).2) (fun p hp => hTime p hp)
      (mul_nonneg (add_nonneg hR.le hH.le) hNorm)
      (fun p _ => ⟨(hRawU p).1.trans hKR,(hRawU p).2.1.trans hKR⟩)
      (holderBound_mono_const hHighU.1 hKH) (holderBound_mono_const hHighU.2 hKH)
    have hScaleN : N*((R+H)*‖u.val‖) ≤ E*‖u.val‖ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hNE hNorm
    simp only [F05LocalJetExtension,hν]
    exact schauderBound_mono_const hSchauder hScaleN

end Yau.Proofs.F05Aux

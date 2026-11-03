import Yau.Proofs.F05JetExtension
import Yau.Proofs.F05JetCutoffBounds
import Yau.Proofs.F05ReflectionJets

/-! The actual local extension has a fixed operator budget, uniform in the
time slab and physical FTC jet. No norm is assigned by an unchecked supremum. -/

open Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_local_extension_raw_low_budget (A : AtlasData M) (i : Fin A.count)
    (φ : Space n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hSupport : tsupport φ ⊆ Metric.closedBall 0 1) :
    ∃ E : ℝ, 0 < E ∧ ∀ (α : ℝ), 0 < α → α < 1 → ∀ (T : ℝ) (hT : 0 < T)
      (u : F05LocalFTCGraph A i α hT.le),
      let U := F05LocalJetExtension A i φ u.val
      C2 (cylinder univ 0 T) U ∧
        (∀ p ∈ cylinder univ 0 T, |U p| ≤ E*‖u.val‖ ∧
          ‖spatialD U p‖ ≤ E*‖u.val‖ ∧ ‖spatialDD U p‖ ≤ E*‖u.val‖ ∧
          |timeD (cylinder univ 0 T) U p| ≤ E*‖u.val‖) ∧
        HolderBound α (cylinder univ 0 T) (fun p => (U p,spatialD U p)) (E*‖u.val‖) := by
  have hc : HasCompactSupport φ :=
    (isCompact_closedBall (0 : Space n) 1).of_isClosed_subset (isClosed_tsupport φ) hSupport
  obtain ⟨C,hC,hCutoff⟩ := F05_cutoff_jet_raw_bound φ hφ hc
  refine ⟨8000*C,by positivity,?_⟩
  intro α hα hα1 T hT u
  have hK : 0 ≤ C*‖u.val‖ := mul_nonneg hC.le (norm_nonneg _)
  have hRaw := hCutoff α (F05Q A i T) u.val
  cases hν : A.normal i with
  | none =>
    have hOpen := F05ModelOpen_none A i hν
    have hJets := F05_local_extension_jets A i α hT u φ hφ hSupport
    simp only [F05LocalJetExtension,hν] at hJets ⊢
    rw [hOpen,closure_univ] at hJets
    have hGlobalRaw : ∀ p ∈ cylinder univ 0 T,
        |F05CutoffJetValue φ u.val p| ≤ C*‖u.val‖ ∧
          ‖spatialD (F05CutoffJetValue φ u.val) p‖ ≤ C*‖u.val‖ ∧
          ‖spatialDD (F05CutoffJetValue φ u.val) p‖ ≤ C*‖u.val‖ ∧
          |timeD (cylinder univ 0 T) (F05CutoffJetValue φ u.val) p| ≤ C*‖u.val‖ := by
      intro p hp
      rw [hJets.2.2.1 hp,hJets.2.2.2.1 hp,hJets.2.2.2.2 hp]
      exact hRaw p
    have hLow := c2_global_lowPair_holder hα hα1 hT hK hJets.1
      (fun p hp => ⟨(hGlobalRaw p hp).1,(hGlobalRaw p hp).2.2.1,(hGlobalRaw p hp).2.2.2⟩)
    have hScale : C*‖u.val‖ ≤ (8000*C)*‖u.val‖ := by nlinarith
    have hScaleLow : 16*(C*‖u.val‖) ≤ (8000*C)*‖u.val‖ := by nlinarith
    refine ⟨hJets.1,?_,holderBound_mono_const hLow hScaleLow⟩
    intro p hp
    have h := hGlobalRaw p hp
    exact ⟨h.1.trans hScale,h.2.1.trans hScale,h.2.2.1.trans hScale,h.2.2.2.trans hScale⟩
  | some j =>
    have hOpen := F05ModelOpen_some A i hν
    have hClosed := F05ModelClosed_some A i hν
    have hCont := F05_cutoff_jet_continuousOn A i α T φ hφ hSupport u.val
    have hSpace (p : Point n) := F05_cutoff_jet_derivatives_model A i α hT.le u φ hφ hSupport (p := p)
    have hTime (p : Point n) := F05_cutoff_jet_time_model A i α hT.le u φ hSupport (p := p)
    rw [hClosed] at hCont hTime
    rw [hOpen] at hSpace
    have hNative := F05_reflection_jet_bounds
      (show ‖(-realVec j : Space n)‖ = 1 by simp only [norm_neg,realVec_norm]) hα hα1 hT hK
      (F05CutoffJetValue φ u.val) (F05CutoffJetGradient φ u.val)
      (F05CutoffJetHessian φ u.val) (F05CutoffJetTime φ u.val)
      hCont.1 hCont.2.1 hCont.2.2.1 hCont.2.2.2
      (fun p hp => (hSpace p hp).1) (fun p hp => (hSpace p hp).2) (fun p hp => hTime p hp)
      (fun p _ => hRaw p)
    simp only [F05LocalJetExtension,hν]
    refine ⟨hNative.1,?_,?_⟩
    · intro p hp
      have h := hNative.2.2.2.2.2.1 p hp
      have hScale : 500*(C*‖u.val‖) ≤ (8000*C)*‖u.val‖ := by nlinarith
      exact ⟨h.1.trans hScale,h.2.1.trans hScale,h.2.2.1.trans hScale,h.2.2.2.trans hScale⟩
    · convert hNative.2.2.2.2.2.2 using 1 <;> ring

end Yau.Proofs.F05Aux

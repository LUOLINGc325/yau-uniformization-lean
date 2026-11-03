import Yau.Proofs.F05JetExtension
import Yau.Proofs.F05JetInitialTotal
import Yau.Proofs.F05ReflectionTime

/-! The concrete extension preserves all four zero initial jets, including
the one-sided time derivative on the closed initial face. -/

open Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_local_extension_initial_value (A : AtlasData M) (i : Fin A.count)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u : F05LocalZeroFTCGraph A i α hT)
    (φ : Space n → ℝ) (z : Space n) : F05LocalJetExtension A i φ u.val (z,0) = 0 := by
  have hV (w : Space n) : F05CutoffJetValue φ u.val (w,0) = 0 := by
    unfold F05CutoffJetValue
    rw [(F05LocalZeroFTCGraph_initial_total A i α hT u w).1,mul_zero]
  cases hν : A.normal i with
  | none => simpa only [F05LocalJetExtension,hν] using hV z
  | some j =>
    simpa only [F05LocalJetExtension,hν] using F05_reflection_zero_slice
      (show ‖(-realVec j : Space n)‖ = 1 by simp only [norm_neg,realVec_norm])
      (fun w _ => hV w) z

theorem F05_local_extension_initial_time (A : AtlasData M) (i : Fin A.count)
    (α : ℝ) {T : ℝ} (hT : 0 < T) (u : F05LocalZeroFTCGraph A i α hT.le)
    (φ : Space n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hSupport : tsupport φ ⊆ Metric.closedBall 0 1) (z : Space n) :
    timeD (cylinder univ 0 T) (F05LocalJetExtension A i φ u.val) (z,0) = 0 := by
  have hK (w : Space n) : F05CutoffJetTime φ u.val (w,0) = 0 := by
    unfold F05CutoffJetTime
    rw [(F05LocalZeroFTCGraph_initial_total A i α hT.le u w).2.2.2,mul_zero]
  let uFTC : F05LocalFTCGraph A i α hT.le := ⟨u.val,u.property.1.1.1⟩
  cases hν : A.normal i with
  | none =>
    have hOpen := F05ModelOpen_none A i hν
    have hJets := F05_local_extension_jets A i α hT uFTC φ hφ hSupport
    rw [hOpen,closure_univ] at hJets
    exact (hJets.2.2.2.2 ⟨mem_univ z,le_rfl,hT.le⟩).trans (hK z)
  | some j =>
    have hClosed := F05ModelClosed_some A i hν
    have hTime (p : Point n) :=
      F05_cutoff_jet_time_model A i α hT.le uFTC φ hSupport (p := p)
    rw [hClosed] at hTime
    simp only [F05LocalJetExtension,hν]
    rw [F05_reflection_timeD
      (show ‖(-realVec j : Space n)‖ = 1 by simp only [norm_neg,realVec_norm]) hT
      (fun p hp => hTime p hp) (p := (z,0)) ⟨le_rfl,hT.le⟩]
    exact F05_reflection_zero_slice
      (show ‖(-realVec j : Space n)‖ = 1 by simp only [norm_neg,realVec_norm])
      (fun w _ => hK w) z

theorem F05_local_extension_initial_spatial (A : AtlasData M) (i : Fin A.count)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u : F05LocalZeroFTCGraph A i α hT)
    (φ : Space n → ℝ) (z : Space n) :
    spatialD (F05LocalJetExtension A i φ u.val) (z,0) = 0 ∧
      spatialDD (F05LocalJetExtension A i φ u.val) (z,0) = 0 := by
  have hV : (fun w => F05LocalJetExtension A i φ u.val (w,0)) = fun _ => 0 :=
    funext (F05_local_extension_initial_value A i α hT u φ)
  simp [spatialD,spatialDD,hV]

end Yau.Proofs.F05Aux

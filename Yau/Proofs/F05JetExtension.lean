import Yau.Proofs.F05JetCutoffDerivatives
import Yau.Proofs.F05GlobalJets
import Yau.Proofs.F05Reflection

/-! A physical FTC jet has an actual C2 extension through both the artificial
chart rim and the genuine model boundary, with all four jets preserved. -/

open Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05LocalJetExtension (A : AtlasData M) (i : Fin A.count) {α T : ℝ}
    (φ : Space n → ℝ) (u : F05JetComponent α (F05Q A i T)) : Point n → ℝ :=
  match A.normal i with
  | none => F05CutoffJetValue φ u
  | some j => halfSpaceSecondOrderExtension (-realVec j) (F05CutoffJetValue φ u)

theorem F05ModelOpen_none (A : AtlasData M) (i : Fin A.count) (hν : A.normal i = none) :
    F05ModelOpen A i = univ := by simp only [F05ModelOpen,hν]

theorem F05ModelOpen_some (A : AtlasData M) (i : Fin A.count) {j : RIdx n}
    (hν : A.normal i = some j) : F05ModelOpen A i = {z | 0 < inner ℝ (-realVec j) z} := by
  ext z
  have hr : inner ℝ (realVec j) z = realCoord z j := realCoordLinear_apply j z
  simp only [F05ModelOpen,hν,mem_setOf_eq,inner_neg_left,hr,neg_pos]

theorem F05ModelClosed_some (A : AtlasData M) (i : Fin A.count) {j : RIdx n}
    (hν : A.normal i = some j) :
    closure (F05ModelOpen A i) = {z | 0 ≤ inner ℝ (-realVec j) z} := by
  rw [F05ModelOpen_eq,F05FlatOpen_closure]
  ext z
  have hr : inner ℝ (realVec j) z = realCoord z j := realCoordLinear_apply j z
  simp only [hν,mem_setOf_eq,inner_neg_left,hr,neg_nonneg]

theorem F05_local_extension_jets (A : AtlasData M) (i : Fin A.count)
    (α : ℝ) {T : ℝ} (hT : 0 < T) (u : F05LocalFTCGraph A i α hT.le)
    (φ : Space n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hSupport : tsupport φ ⊆ Metric.closedBall 0 1) :
    let U := F05LocalJetExtension A i φ u.val
    let Q := cylinder (closure (F05ModelOpen A i)) 0 T
    C2 (cylinder univ 0 T) U ∧ EqOn U (F05CutoffJetValue φ u.val) Q ∧
      EqOn (spatialD U) (F05CutoffJetGradient φ u.val) Q ∧
      EqOn (spatialDD U) (F05CutoffJetHessian φ u.val) Q ∧
      EqOn (timeD (cylinder univ 0 T) U) (F05CutoffJetTime φ u.val) Q := by
  have hCont := F05_cutoff_jet_continuousOn A i α T φ hφ hSupport u.val
  have hSpace (p : Point n) := F05_cutoff_jet_derivatives_model A i α hT.le u φ hφ hSupport (p := p)
  have hTime (p : Point n) := F05_cutoff_jet_time_model A i α hT.le u φ hSupport (p := p)
  cases hν : A.normal i with
  | none =>
    have hOpen := F05ModelOpen_none A i hν
    rw [hOpen,closure_univ] at hCont hTime
    rw [hOpen] at hSpace
    have hGlobal := F05_c2_of_global_jets hT
      (F05CutoffJetValue φ u.val) (F05CutoffJetGradient φ u.val)
      (F05CutoffJetHessian φ u.val) (F05CutoffJetTime φ u.val)
      hCont.1 hCont.2.1 hCont.2.2.1 hCont.2.2.2
      (fun p hp => (hSpace p hp).1) (fun p hp => (hSpace p hp).2) (fun p hp => hTime p hp)
    simpa only [F05LocalJetExtension,hν,hOpen,closure_univ] using
      (show C2 (cylinder univ 0 T) (F05CutoffJetValue φ u.val) ∧
        EqOn (F05CutoffJetValue φ u.val) (F05CutoffJetValue φ u.val) (cylinder univ 0 T) ∧
        EqOn (spatialD (F05CutoffJetValue φ u.val)) (F05CutoffJetGradient φ u.val) (cylinder univ 0 T) ∧
        EqOn (spatialDD (F05CutoffJetValue φ u.val)) (F05CutoffJetHessian φ u.val) (cylinder univ 0 T) ∧
        EqOn (timeD (cylinder univ 0 T) (F05CutoffJetValue φ u.val))
          (F05CutoffJetTime φ u.val) (cylinder univ 0 T) from
        ⟨hGlobal.1,fun _ _ => rfl,hGlobal.2⟩)
  | some j =>
    have hOpen := F05ModelOpen_some A i hν
    have hClosed := F05ModelClosed_some A i hν
    rw [hClosed] at hCont hTime
    rw [hOpen] at hSpace
    have hNative := halfSpaceSecondOrderExtension_jets
      (show ‖(-realVec j : Space n)‖ = 1 by simp only [norm_neg,realVec_norm]) hT
      (F05CutoffJetValue φ u.val) (F05CutoffJetGradient φ u.val)
      (F05CutoffJetHessian φ u.val) (F05CutoffJetTime φ u.val)
      hCont.1 hCont.2.1 hCont.2.2.1 hCont.2.2.2
      (fun p hp => (hSpace p hp).1) (fun p hp => (hSpace p hp).2) (fun p hp => hTime p hp)
    simpa only [F05LocalJetExtension,hν,hClosed] using hNative

end Yau.Proofs.F05Aux

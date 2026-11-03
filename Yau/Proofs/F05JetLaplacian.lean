import Yau.Proofs.F05JetOperatorHolder
import Yau.Proofs.F05JetOperatorLinear

/-! The actual Laplacian of a compatible jet is linear and has a fixed
Holder operator bound on every full physical chart. -/

open Set
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05JetLaplacian (A : AtlasData M) (h : ℝ → HermitianField M)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u : F05CompatibleJetGraph A α hT)
    (i : Fin A.count) (p : Point n) : ℝ :=
  F05BCFFun (u.val i).val.2.2.2.val.1 p-F05JetOperator A (fun _ _ => 1) h α hT u i p

def F05JetLaplacianEval (A : AtlasData M) (h : ℝ → HermitianField M)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (i : Fin A.count) (p : F05Q A i T) :
    F05CompatibleJetGraph A α hT →L[ℝ] ℝ :=
  (F05GlobalTimeEval A α hT i p).comp (F05CompatibleJetGraph A α hT).subtypeL-
    F05JetOperatorEval A (fun _ _ => 1) h α hT i p

theorem F05JetLaplacianEval_apply (A : AtlasData M) (h : ℝ → HermitianField M)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (i : Fin A.count) (p : F05Q A i T)
    (u : F05CompatibleJetGraph A α hT) :
    F05JetLaplacianEval A h α hT i p u = F05JetLaplacian A h α hT u i p.val := by
  change (u.val i).val.2.2.2.val.1 p-F05JetOperatorEval A (fun _ _ => 1) h α hT i p u = _
  rw [F05JetOperatorEval_apply]
  exact congrArg (fun s => s-F05JetOperator A (fun _ _ => 1) h α hT u i p.val)
    (F05BCFFun_apply (u.val i).val.2.2.2.val.1 p).symm

theorem F05JetLaplacian_sub (A : AtlasData M) (h : ℝ → HermitianField M)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u v : F05CompatibleJetGraph A α hT)
    (i : Fin A.count) (p : F05Q A i T) :
    F05JetLaplacian A h α hT (u-v) i p.val =
      F05JetLaplacian A h α hT u i p.val-F05JetLaplacian A h α hT v i p.val := by
  rw [← F05JetLaplacianEval_apply A h α hT i p (u-v),map_sub,
    F05JetLaplacianEval_apply,F05JetLaplacianEval_apply]

theorem F05JetLaplacian_eq_intrinsic {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (h : ℝ → HermitianField M) (α : ℝ) {T : ℝ} (hT : 0 < T)
    (u : F05CompatibleJetGraph A α hT.le) (i : Fin A.count) {p : Point n} (hp : p ∈ F05Q A i T) :
    F05JetLaplacian A h α hT.le u i p =
      laplacian (h p.2) (fun y => F05CanonicalJetFunction A χ α hT.le u y p.2) (lift A i p.1) := by
  have hReal := F05CanonicalJetFunction_realizes hA hχ α hT u i
  have hTime := (hReal.2.2.2 hp).symm.trans
    (F05_timeD_pull A i T (F05CanonicalJetFunction A χ α hT.le u) (p := p) hp.1)
  unfold F05JetLaplacian
  rw [F05JetOperator_eq_intrinsic hA hχ (fun _ _ => 1) h α hT u i hp]
  dsimp only [F05IntrinsicLinearOperator]
  rw [hTime]
  ring

theorem F05_jet_laplacian_holder_uniform {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (h : ℝ → HermitianField M) {S : ℝ} (hS : 0 < S) (hh : MetricFamilySmooth h (Icc 0 S))
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ) (hT : 0 < T), T ≤ S → T ≤ 1 →
      ∀ u : F05CompatibleJetGraph A α hT.le, ∀ i : Fin A.count,
        HolderBound α (F05Q A i T) (F05JetLaplacian A h α hT.le u i) (C*‖u‖) := by
  obtain ⟨C,hC,hOp⟩ := F05_jet_operator_holder_uniform hA hχ h (fun _ _ => 1) hS hh
    (fun _ => contDiffOn_const) hα hα1
  refine ⟨1+C,by positivity,?_⟩
  intro T hT hTS hT1 u i
  have hNorm : ‖(u.val i).val‖ ≤ ‖u‖ := norm_le_pi_norm u.val i
  have hTime := holderBound_mono_const (F05JetComponent_time_holderBound (u.val i).val) hNorm
  have hBound := holderBound_sub hTime (hOp T hT hTS hT1 u i)
  unfold F05JetLaplacian
  convert hBound using 1
  ring

end Yau.Proofs.F05Aux

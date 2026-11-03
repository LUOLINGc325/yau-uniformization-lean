import Yau.Proofs.F05JetCutoffContinuity
import Yau.LeafProofs.L16CutoffFullHolderExtension

/-! The four literal Hessian product terms have genuine Holder bounds on an
arbitrary physical set. The native bilinear extension estimates handle all
cross-pairs at the artificial rim. -/

open Set
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

local instance f05_highCutoffDualGroup : NormedAddCommGroup (F05Dual n) := inferInstance
local instance f05_highCutoffDualSpace : NormedSpace ℝ (F05Dual n) := inferInstance
local instance f05_highCutoffHessianGroup : NormedAddCommGroup (F05Hessian n) := f05_jetHessianGroup
local instance f05_highCutoffHessianSpace : NormedSpace ℝ (F05Hessian n) := f05_jetHessianSpace

theorem F05_cutoff_jet_high_holder {α P K : ℝ} {U Q Q₀ : Set (Point n)}
    (φ : Space n → ℝ) (u : F05JetComponent α Q₀)
    (hφ₀ : HolderBound α Q (fun p => φ p.1) P)
    (hφ₁ : HolderBound α Q (fun p => fderiv ℝ φ p.1) P)
    (hφ₂ : HolderBound α Q (fun p => fderiv ℝ (fderiv ℝ φ) p.1) P)
    (hV : HolderBound α (U∩Q) (F05BCFFun u.1) K)
    (hG : HolderBound α (U∩Q) (F05BCFFun u.2.1) K)
    (hH : HolderBound α (U∩Q) (F05BCFFun u.2.2.1.val.1) K)
    (hTime : HolderBound α (U∩Q) (F05BCFFun u.2.2.2.val.1) K)
    (hOutside : ∀ p ∈ Q, p ∉ U → φ p.1 = 0 ∧ fderiv ℝ φ p.1 = 0 ∧
      fderiv ℝ (fderiv ℝ φ) p.1 = 0) :
    HolderBound α Q (F05CutoffJetHessian φ u) (8*P*K) ∧
      HolderBound α Q (F05CutoffJetTime φ u) (8*P*K) := by
  have h₀ := holderBound_smul_cutoff_extension hφ₀ hH (fun p hp hout => (hOutside p hp hout).1)
  have h₁ := holderBound_tensor_cutoff_extension hφ₁ hG (fun p hp hout => (hOutside p hp hout).2.1)
  have h₂ := holderBound_tensor_flip_cutoff_extension hφ₁ hG (fun p hp hout => (hOutside p hp hout).2.1)
  have h₃ := holderBound_bilinear_cutoff_extension
    (fun (a : F05Hessian n) (v : ℝ) => v • a)
    (fun x y z => smul_sub z x y) (fun x y z => sub_smul y z x)
    (fun z => smul_zero z)
    (fun a v => by rw [norm_smul,Real.norm_eq_abs,mul_comm])
    hφ₂ hV (fun p hp hout => (hOutside p hp hout).2.2)
  have hSum := holderBound_add (holderBound_add (holderBound_add h₀ h₁) h₂) h₃
  have hBudget : (2*P*K+2*P*K+2*P*K)+2*P*K = 8*P*K := by ring
  rw [hBudget] at hSum
  have hT := holderBound_smul_cutoff_extension hφ₀ hTime (fun p hp hout => (hOutside p hp hout).1)
  refine ⟨hSum,?_⟩
  unfold F05CutoffJetTime
  simpa only [smul_eq_mul] using
    holderBound_mono_const hT (by nlinarith [mul_nonneg hφ₀.1 hTime.1])

end Yau.Proofs.F05Aux

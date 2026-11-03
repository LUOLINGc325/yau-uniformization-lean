import Yau.Proofs.F01TensorDilation

/-! Recover the original spatial jet from its genuine rescaled tensor.
The inverse operator has a finite numerical budget fixed before the
function, domain and point; order and dimension zero are included. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem spatialTensorDilation_inv_apply (k : ℕ) {ρ : ℝ} (hρ : ρ ≠ 0)
    (D : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F) :
    spatialTensorDilation k ρ⁻¹ (spatialTensorDilation k ρ D) = D := by
  ext v
  change D (fun i => ρ • (ρ⁻¹ • v i)) = D v
  simp only [smul_smul, mul_inv_cancel₀ hρ, one_smul]

theorem inverse_spatial_jet_budget (k : ℕ) {ρ : ℝ} (hρ : ρ ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Set E) (f : E → F) (x : E) (B : ℝ),
      IsOpen S → ContDiffOn ℝ ∞ f S → ρ • x ∈ S →
      ‖iteratedFDeriv ℝ k (fun z => f (ρ • z)) x‖ ≤ B →
      ‖iteratedFDeriv ℝ k f (ρ • x)‖ ≤ C * B := by
  let L := spatialTensorDilation (E := E) (F := F) k ρ⁻¹
  have hL : 0 ≤ ‖L‖ := ContinuousLinearMap.opNorm_nonneg L
  refine ⟨1 + ‖L‖, by linarith, ?_⟩
  intro S f x B hS hf hx hBound
  have hB : 0 ≤ B := (norm_nonneg _).trans hBound
  have he := iteratedFDeriv_spatial_dilation k ρ hS hf hx
  have hInv := spatialTensorDilation_inv_apply k hρ (iteratedFDeriv ℝ k f (ρ • x))
  calc
    _ = ‖L (spatialTensorDilation k ρ (iteratedFDeriv ℝ k f (ρ • x)))‖ := congrArg norm hInv.symm
    _ ≤ ‖L‖ * ‖spatialTensorDilation k ρ (iteratedFDeriv ℝ k f (ρ • x))‖ := L.le_opNorm _
    _ ≤ ‖L‖ * B := mul_le_mul_of_nonneg_left (he ▸ hBound) hL
    _ ≤ (1 + ‖L‖) * B := by nlinarith

end Yau.NodeProofs.F01Aux

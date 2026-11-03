import Yau.Proofs.F01SpatialWordsTensorJets

/-! Spatial dilation acts on the actual kth tensor by bounded linear
precomposition. Its operator norm is at most one at every admissible
small scale, including dimension and tensor order zero. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

def spatialTensorDilation (k : ℕ) (ρ : ℝ) :
    (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F) →L[ℝ]
      (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F) :=
  ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin k => ρ • ContinuousLinearMap.id ℝ E)

theorem spatialTensorDilation_norm_le_one (k : ℕ) {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    ‖spatialTensorDilation (E := E) (F := F) k ρ‖ ≤ 1 := by
  have hL : ‖ρ • ContinuousLinearMap.id ℝ E‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖ρ • x‖ ≤ 1 * ‖x‖
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hρ (norm_nonneg _)
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMapL_le F _).trans
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hL)

theorem iteratedFDeriv_spatial_dilation {f : E → F} {S : Set E} {x : E} (k : ℕ) (ρ : ℝ)
    (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ f S) (hx : ρ • x ∈ S) :
    iteratedFDeriv ℝ k (fun z => f (ρ • z)) x =
      spatialTensorDilation k ρ (iteratedFDeriv ℝ k f (ρ • x)) := by
  let L : E →L[ℝ] E := ρ • ContinuousLinearMap.id ℝ E
  have hPre : IsOpen (L ⁻¹' S) := hS.preimage L.continuous
  have he := L.iteratedFDerivWithin_comp_right hf hS.uniqueDiffOn hPre.uniqueDiffOn
    hx (by simp : (k : ℕ∞ω) ≤ ∞)
  rw [iteratedFDerivWithin_of_isOpen k hPre hx,
    iteratedFDerivWithin_of_isOpen k hS (show L x ∈ S from hx)] at he
  exact he

open Yau Yau.Parabolic
variable {n : ℕ}

theorem holderBound_spatialTensorDilation {Q : Set (Point n)} {β C ρ : ℝ} (k : ℕ)
    {J : Point n → ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F}
    (hJ : HolderBound β Q J C) (hρ : |ρ| ≤ 1) :
    HolderBound β Q (fun p => spatialTensorDilation k ρ (J p)) C := by
  have hb := holderBound_continuousLinearMap hJ (spatialTensorDilation (E := E) (F := F) k ρ)
  apply holderBound_mono_const hb
  exact (mul_le_mul_of_nonneg_right (spatialTensorDilation_norm_le_one k hρ) hJ.1).trans_eq
    (one_mul C)

end Yau.NodeProofs.F01Aux

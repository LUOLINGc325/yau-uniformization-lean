import Yau.Proofs.F01AffineClockHolder
import Yau.Proofs.F01DilatedAffineTensorHolder
import Yau.Proofs.F01AffineParabolicHolder

/-! Actual spatial tensor jets of a dilated affine-time background
have uniform parabolic Holder constants before centers, scales and
bounded time parameters. No positive-time clamping is introduced. -/
noncomputable section
open Set Metric
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {ι F : Type*}
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance shiftedAffineTensorEndNormed (k : ℕ) :
    NormedAddCommGroup ((ContinuousMultilinearMap ℝ (fun _ : Fin k => Space n) F) →L[ℝ]
      (ContinuousMultilinearMap ℝ (fun _ : Fin k => Space n) F)) := ContinuousLinearMap.toNormedAddCommGroup

local instance shiftedAffineTensorEndSpace (k : ℕ) :
    NormedSpace ℝ ((ContinuousMultilinearMap ℝ (fun _ : Fin k => Space n) F) →L[ℝ]
      (ContinuousMultilinearMap ℝ (fun _ : Fin k => Space n) F)) := ContinuousLinearMap.toNormedSpace

local instance shiftedAffineTensorSmulOpNorm (k : ℕ) :
    Norm (ℝ →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin k => Space n) F) →L[ℝ]
      (ContinuousMultilinearMap ℝ (fun _ : Fin k => Space n) F)) := ContinuousLinearMap.hasOpNorm

theorem dilated_spatial_tensor_holder_budget {f : ι → Space n → F} {r β : ℝ} (k : ℕ)
    (hf : UniformJetBounds (k + 1) f (fun _ => ball 0 r))
    (hfs : ∀ i, ContDiffOn ℝ ∞ (f i) (ball 0 r)) (hβ : β ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → ρ ≤ 1 → ∀ i,
      HolderBound β (cylinder (ball (0 : Space n) 1) (-1) 1)
        (fun p => iteratedFDeriv ℝ k (fun z => f i (ρ • z)) p.1) K := by
  obtain ⟨K, hK, hBudget⟩ := dilated_affine_spatial_tensor_holder_budget k hf hf hfs hfs hβ
  refine ⟨K, hK, ?_⟩
  intro ρ hρ hρr hρ1 i
  simpa only [zero_smul, smul_zero, add_zero] using
    hBudget ρ hρ hρr hρ1 0 (by norm_num) i

theorem shifted_affine_spatial_tensor_holder_budget {f g : ι → Space n → F}
    {r β T : ℝ} (k : ℕ) (hT : 0 ≤ T)
    (hf : UniformJetBounds (k + 1) f (fun _ => ball 0 r))
    (hg : UniformJetBounds (k + 1) g (fun _ => ball 0 r))
    (hfs : ∀ i, ContDiffOn ℝ ∞ (f i) (ball 0 r))
    (hgs : ∀ i, ContDiffOn ℝ ∞ (g i) (ball 0 r)) (hβ : β ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ρ τ κ : ℝ), 0 < ρ → ρ ≤ r → ρ ≤ 1 →
      |τ| ≤ T → |κ| ≤ 1 → ∀ i,
      HolderBound β (cylinder (ball (0 : Space n) 1) (-1) 1)
        (fun p => iteratedFDeriv ℝ k
          (fun z => f i (ρ • z) + (τ + κ * p.2) • g i (ρ • z)) p.1) K := by
  obtain ⟨Kf, hKf, hF⟩ := dilated_spatial_tensor_holder_budget k hf hfs hβ
  obtain ⟨Kg, hKg, hG⟩ := dilated_spatial_tensor_holder_budget k hg hgs hβ
  obtain ⟨Kt, hKt, hClock⟩ := affine_clock_holder_budget (n := n) hT hβ
  let L : ℝ →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin k => Space n) F) →L[ℝ]
      (ContinuousMultilinearMap ℝ (fun _ : Fin k => Space n) F) := ContinuousLinearMap.lsmul ℝ ℝ
  let C := 2 * ‖L‖ * Kt * Kg
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (ContinuousLinearMap.opNorm_nonneg L)) hKt.le) hKg.le
  refine ⟨Kf + C, by linarith, ?_⟩
  intro ρ τ κ hρ hρr hρ1 hτ hκ i
  have hProd := holderBound_bilinear (hClock τ κ hτ hκ) (hG ρ hρ hρr hρ1 i) L
  have hAdd := holderBound_add (hF ρ hρ hρr hρ1 i) hProd
  apply holderBound_congr_on_native hAdd
  intro p hp
  have hz := spatialDilation_mem_ball hρ hρr hp.1
  have hfa : ContDiffAt ℝ ∞ (fun z : Space n => f i (ρ • z)) p.1 :=
    ((hfs i).contDiffAt (isOpen_ball.mem_nhds hz)).comp p.1 (by fun_prop)
  have hga : ContDiffAt ℝ ∞ (fun z : Space n => g i (ρ • z)) p.1 :=
    ((hgs i).contDiffAt (isOpen_ball.mem_nhds hz)).comp p.1 (by fun_prop)
  dsimp only [L]
  rw [fun_iteratedFDeriv_add_apply (hfa.of_le (by simp))
    ((hga.const_smul (τ + κ * p.2)).of_le (by simp)),
    iteratedFDeriv_const_smul_apply' (hga.of_le (by simp))]
  rfl

end Yau.NodeProofs.F01Aux

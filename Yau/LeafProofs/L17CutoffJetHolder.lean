import Yau.LeafProofs.L17FrozenCoefficientHolder
import Yau.LeafProofs.L17PartitionJetBounds
import Yau.LeafProofs.L17LocalizedSchauderDerivativeNorms

open Set Metric
open scoped ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux

open Yau.Parabolic
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem scale_backgroundChart_jet_bound (A : BoundedChartFamily g)
    {f : M.Carrier → ℝ} (hf : SmoothFn f) {ρ : ℝ} (hρ : 0 < ρ)
    (hρr : 2 * ρ < A.radius) (p : M.Carrier) (k : ℕ) (C : ℝ)
    (hb : ∀ z ∈ ball (0 : ComplexVector n) (2 * ρ),
      ‖iteratedFDeriv ℝ k (fun w => f (A.chart p w)) z‖ ≤ C * (ρ⁻¹)^k)
    {z : ComplexVector n} (hz : z ∈ ball 0 2) :
    ‖iteratedFDeriv ℝ k (fun w => f (A.chart p (ρ • w))) z‖ ≤ C := by
  have hzNorm : ‖z‖ < 2 := by simpa only [mem_ball,dist_zero_right] using hz
  have hScaled : ρ • z ∈ ball (0 : ComplexVector n) (2*ρ) := by
    simpa only [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hρ] using
      (mul_lt_mul_of_pos_left hzNorm hρ).trans_eq (mul_comm ρ 2)
  have hScaledA : ρ • z ∈ ball (0 : ComplexVector n) A.radius :=
    (ball_subset_ball hρr.le) hScaled
  have h := norm_iteratedFDeriv_comp_smul_le isOpen_ball
    (smoothFn_comp_backgroundChart_contDiffOn A hf p) ρ hScaledA k
  rw [Real.norm_eq_abs,abs_of_pos hρ] at h
  calc
    _ ≤ ‖iteratedFDeriv ℝ k (fun w => f (A.chart p w)) (ρ • z)‖ * ρ^k := h
    _ ≤ (C*(ρ⁻¹)^k)*ρ^k := mul_le_mul_of_nonneg_right (hb _ hScaled) (pow_nonneg hρ.le _)
    _ = C := by rw [mul_assoc,← mul_pow,inv_mul_cancel₀ hρ.ne',one_pow,mul_one]

theorem scaled_backgroundChart_jet_holderBound (A : BoundedChartFamily g)
    {f : M.Carrier → ℝ} (hf : SmoothFn f) {ρ : ℝ} (hρ : 0 < ρ)
    (hρr : 2 * ρ < A.radius) (p : M.Carrier) (B : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k)
    (hb : ∀ k z, z ∈ ball (0 : ComplexVector n) (2*ρ) →
      ‖iteratedFDeriv ℝ k (fun w => f (A.chart p w)) z‖ ≤ B k * (ρ⁻¹)^k)
    (k : ℕ) (T γ : ℝ) (hγ : γ ≤ 1) :
    HolderBound γ (cylinder (ball (0 : Space n) 2) 0 T)
      (fun q => iteratedFDeriv ℝ k (fun w => f (A.chart p (ρ • w))) q.1)
      (B k + B (k+1) * (4 : ℝ)^(1-γ)) := by
  let F := fun w => f (A.chart p (ρ • w))
  have hF : ContDiffOn ℝ ∞ F (ball 0 2) := smoothFn_comp_scaledChart_contDiffOn A hf hρ hρr p
  have hjinf : (k : ℕ∞ω) < ∞ := by
    change ((k : ℕ∞) : ℕ∞ω) < ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)
  have hSup : ∀ j z, z ∈ ball (0 : ComplexVector n) 2 → ‖iteratedFDeriv ℝ j F z‖ ≤ B j :=
    fun j z hz => scale_backgroundChart_jet_bound A hf hρ hρr p j (B j) (hb j) hz
  have hDiff : ∀ z ∈ ball (0 : ComplexVector n) 2, DifferentiableAt ℝ (iteratedFDeriv ℝ k F) z :=
    fun z hz => (hF.contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt_iteratedFDeriv hjinf
  have hDeriv : ∀ z ∈ ball (0 : ComplexVector n) 2, ‖fderiv ℝ (iteratedFDeriv ℝ k F) z‖ ≤ B (k+1) := by
    intro z hz
    rw [norm_fderiv_iteratedFDeriv]
    exact hSup (k+1) z hz
  have h := spatialLipschitz_holderBound_ball (T := T) (by norm_num : (0 : ℝ) < 2) hγ (hB k)
    (hB (k+1)) (iteratedFDeriv ℝ k F) (hSup k) (fun z hz w hw =>
      Convex.norm_image_sub_le_of_norm_fderiv_le hDiff hDeriv (convex_ball _ _) hw hz)
  simpa only [show (2 : ℝ)*2=4 by norm_num] using h

theorem scaled_backgroundChart_three_jet_holderBounds (A : BoundedChartFamily g)
    {f : M.Carrier → ℝ} (hf : SmoothFn f) {ρ : ℝ} (hρ : 0 < ρ)
    (hρr : 2 * ρ < A.radius) (p : M.Carrier) (B : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k)
    (hb : ∀ k z, z ∈ ball (0 : ComplexVector n) (2*ρ) →
      ‖iteratedFDeriv ℝ k (fun w => f (A.chart p w)) z‖ ≤ B k * (ρ⁻¹)^k)
    (T γ : ℝ) (hγ : γ ≤ 1) :
    let F := fun w => f (A.chart p (ρ • w))
    let Q := cylinder (ball (0 : Space n) 2) 0 T
    HolderBound γ Q (fun q => F q.1) (B 0+B 1*(4 : ℝ)^(1-γ)) ∧
    HolderBound γ Q (fun q => fderiv ℝ F q.1) (B 1+B 2*(4 : ℝ)^(1-γ)) ∧
    HolderBound γ Q (fun q => fderiv ℝ (fderiv ℝ F) q.1) (B 2+B 3*(4 : ℝ)^(1-γ)) := by
  dsimp only
  have h0 := scaled_backgroundChart_jet_holderBound A hf hρ hρr p B hB hb 0 T γ hγ
  have h1 := scaled_backgroundChart_jet_holderBound A hf hρ hρr p B hB hb 1 T γ hγ
  have h2 := scaled_backgroundChart_jet_holderBound A hf hρ hρr p B hB hb 2 T γ hγ
  refine ⟨?_,?_,?_⟩
  · simpa only [HolderBound,norm_iteratedFDeriv_zero,L17LocalizedSchauderAux.norm_iteratedFDeriv_zero_sub]
      using h0
  · simpa only [HolderBound,norm_iteratedFDeriv_one,L17LocalizedSchauderAux.norm_iteratedFDeriv_one_sub]
      using h1
  · simpa only [HolderBound,L17LocalizedSchauderAux.norm_iteratedFDeriv_two_sub,
      ← norm_iteratedFDeriv_fderiv (n := 1),norm_iteratedFDeriv_one] using h2

end Yau.LeafProofs.L17Aux

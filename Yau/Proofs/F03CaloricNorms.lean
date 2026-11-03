import Yau.Proofs.F03CaloricMembership

/-! Exact real L² norm identities and the actual product/Pi source norm. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau Parabolic

theorem real_norm_toLp_sq_eq_integral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖^2=∫ p,(f p)^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with p hp
  simp only [hp,RCLike.inner_apply,conj_trivial,pow_two]

theorem real_norm_toLp_le_sqrt_mul {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : MemLp f 2 μ) (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hIntegral : (∫ p,(f p)^2 ∂μ) ≤ C*B^2) : ‖hf.toLp f‖ ≤ Real.sqrt C*B := by
  have hsq : ‖hf.toLp f‖^2 ≤ (Real.sqrt C*B)^2 := by
    rw [real_norm_toLp_sq_eq_integral μ f hf,mul_pow,Real.sq_sqrt hC]
    exact hIntegral
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hB)).mp hsq

theorem caloricAmbient_norm_le {d : ℕ} (D : Set (Point d)) (e : CaloricAmbient D)
    (B : ℝ) (hB : 0 ≤ B) (hu : ‖e.1‖ ≤ B) (hG : ∀ i, ‖e.2 i‖ ≤ B) : ‖e‖ ≤ B := by
  rw [Prod.norm_def]
  exact max_le hu ((pi_norm_le_iff_of_nonneg hB).mpr hG)

end Yau.Proofs.F03Aux

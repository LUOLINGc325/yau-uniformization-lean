import Yau.Proofs.V02SpanningDisc
import Yau.Proofs.V03CompactImmersionCoefficient
import Yau.Proofs.V03AmbientSmooth

/-! Derivative bounds for actual chart-smooth coefficients along arbitrary
cotangent discs contained in an intrinsic compact set. -/

open scoped Topology ContDiff Manifold
open Filter

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

theorem norm_fderiv_le_of_relative_lipschitz
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : ℂ → F} {X : ℂ → E} {z : ℂ} {C : ℝ}
    (hu : DifferentiableAt ℝ u z) (hX : ContDiffAt ℝ ∞ X z) (hC : 0 ≤ C)
    (hrel : ∀ᶠ w in 𝓝 z, ‖u w - u z‖ ≤ C * ‖X w - X z‖) :
    ‖fderiv ℝ u z‖ ≤ C * (‖fderiv ℝ X z‖ + 1) := by
  let A : NNReal := ‖fderiv ℝ X z‖₊ + 1
  obtain ⟨S, hS, hLip⟩ := (hX.hasStrictFDerivAt (by simp)).exists_lipschitzOnWith_of_nnnorm_lt
    A (by simp [A])
  apply hu.hasFDerivAt.le_of_lip' (mul_nonneg hC (by positivity))
  filter_upwards [hrel, hS] with w hw hwS
  have h := hLip.norm_sub_le hwS (mem_of_mem_nhds hS)
  calc
    ‖u w - u z‖ ≤ C * ‖X w - X z‖ := hw
    _ ≤ C * ((A : ℝ) * ‖w - z‖) := mul_le_mul_of_nonneg_left h hC
    _ = _ := by simp [A, mul_assoc]

theorem real_fderiv_norm_le_complex_one
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] {X : ℂ → F} {z : ℂ}
    (hX : DifferentiableAt ℂ X z) :
    ‖fderiv ℝ X z‖ ≤ ‖fderiv ℂ X z 1‖ := by
  rw [hX.fderiv_restrictScalars ℝ, ContinuousLinearMap.norm_restrictScalars]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  calc
    ‖fderiv ℂ X z v‖ = ‖v • fderiv ℂ X z 1‖ := by
      rw [← map_smul]; simp
    _ = ‖v‖ * ‖fderiv ℂ X z 1‖ := norm_smul _ _
    _ ≤ _ := le_of_eq (mul_comm _ _)

variable {n q : ℕ} {M : ComplexManifold n}

theorem cotangentCoefficient_disc_derivative_control
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {b : CotangentPoint M → ℂ}
    (hb : ∀ x, ContDiffOn ℝ ∞ (fun z => b (cotangentChartInv x z)) (cotangentTarget x))
    {K : Set (CotangentPoint M)} (hK : CotangentCompact K) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ (∀ y ∈ K, ‖b y‖ ≤ B) ∧
      ∀ (f : ℂ → CotangentPoint M), CotangentDisc f →
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, f z ∈ K) →
      ∀ z ∈ Metric.ball (0 : ℂ) 1,
        ‖fderiv ℝ (fun w => b (f w)) z‖ ≤
          C * (‖fderiv ℂ (fun w => G (f w)) z 1‖ + 1) := by
  obtain ⟨C, B, hC, hB, hnorm, hrel⟩ :=
    V03Proof.cotangentCoefficient_compact_control hG hb hK
  refine ⟨C, B, hC, hB, hnorm, fun f hf hfK z hz => ?_⟩
  have hD : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 z :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall
  have hu := (cotangentDisc_comp_real_smooth hf hb).contDiffAt hD
  have hX := (V03Proof.cotangentDisc_ambient_contDiffOn hf hG.1).contDiffAt hD
  have h := norm_fderiv_le_of_relative_lipschitz
    (hu.differentiableAt (by simp)) (hX.restrict_scalars ℝ) hC (by
      filter_upwards [hD] with w hw
      exact hrel _ (hfK w hw) _ (hfK z (Metric.ball_subset_closedBall hz)))
  exact h.trans (mul_le_mul_of_nonneg_left (by
    linarith [real_fderiv_norm_le_complex_one (hX.differentiableAt (by simp))]) hC)

end Yau.Blueprint.V02Proof

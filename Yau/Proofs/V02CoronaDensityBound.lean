import Yau.Proofs.V02CoefficientDerivative
import Yau.Proofs.V02CoronaDbar

/-! Uniform interior bounds for the actual antisymmetric corona density.
All constants are chosen from the intrinsic compact set before the disc. -/

open scoped Topology ContDiff Manifold Matrix
open Filter

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint Yau.LeafProofs

theorem discDbarWithin_norm_le (f : ℂ → ℂ) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    ‖discDbarWithin f z‖ ≤ ‖fderiv ℝ f z‖ := by
  have hx : ‖fderiv ℝ f z 1‖ ≤ ‖fderiv ℝ f z‖ := by
    simpa using (fderiv ℝ f z).le_opNorm (1 : ℂ)
  have hy : ‖fderiv ℝ f z Complex.I‖ ≤ ‖fderiv ℝ f z‖ := by
    simpa using (fderiv ℝ f z).le_opNorm Complex.I
  unfold discDbarWithin
  rw [discEnergyPartial_eq_fderiv _ _ hz, discEnergyPartial_eq_fderiv _ _ hz, norm_mul]
  have hn := norm_add_le (fderiv ℝ f z 1) (Complex.I * fderiv ℝ f z Complex.I)
  simp only [norm_mul, Complex.norm_I, one_mul] at hn
  norm_num only [norm_div, norm_one, Complex.norm_ofNat] at *
  nlinarith

theorem coronaDbarDensity_norm_sq_le
    {ι : Type*} {σ : ι → ℂ → ℂ} {i j : ι} {z : ℂ} {B D : ℝ}
    (hB : 0 ≤ B) (_hD : 0 ≤ D)
    (hi : ‖σ i z‖ ≤ B) (hj : ‖σ j z‖ ≤ B)
    (hdi : ‖discDbarWithin (σ i) z‖ ≤ D)
    (hdj : ‖discDbarWithin (σ j) z‖ ≤ D) :
    ‖coronaDbarDensity σ i j z‖ ^ 2 ≤ 4 * B ^ 2 * D ^ 2 := by
  have hnorm : ‖coronaDbarDensity σ i j z‖ ≤ 2 * B * D := by
    calc
      _ ≤ ‖σ i z * discDbarWithin (σ j) z‖ +
          ‖σ j z * discDbarWithin (σ i) z‖ := norm_sub_le _ _
      _ = ‖σ i z‖ * ‖discDbarWithin (σ j) z‖ +
          ‖σ j z‖ * ‖discDbarWithin (σ i) z‖ := by simp only [norm_mul]
      _ ≤ B * D + B * D := add_le_add
        (mul_le_mul hi hdj (norm_nonneg _) hB)
        (mul_le_mul hj hdi (norm_nonneg _) hB)
      _ = _ := by ring
  have hs := mul_self_le_mul_self (norm_nonneg _) hnorm
  convert hs using 1 <;> ring

variable {n q : ℕ} {M : ComplexManifold n}

theorem finite_cotangentCoefficient_disc_derivative_control
    {ι : Type*} [Fintype ι]
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {b : ι → CotangentPoint M → ℂ}
    (hb : ∀ i x, ContDiffOn ℝ ∞ (fun z => b i (cotangentChartInv x z)) (cotangentTarget x))
    {K : Set (CotangentPoint M)} (hK : CotangentCompact K) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ (∀ i y, y ∈ K → ‖b i y‖ ≤ B) ∧
      ∀ (f : ℂ → CotangentPoint M), CotangentDisc f →
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, f z ∈ K) →
      ∀ i z, z ∈ Metric.ball (0 : ℂ) 1 →
        ‖fderiv ℝ (fun w => b i (f w)) z‖ ≤
          C * (‖fderiv ℂ (fun w => G (f w)) z 1‖ + 1) := by
  classical
  choose C B hC hB hnorm hder using
    fun i => cotangentCoefficient_disc_derivative_control hG (hb i) hK
  refine ⟨∑ i, C i, ∑ i, B i, Finset.sum_nonneg (fun i _ => hC i),
    Finset.sum_nonneg (fun i _ => hB i), ?_, ?_⟩
  · intro i y hy
    exact (hnorm i y hy).trans (Finset.single_le_sum (fun i _ => hB i) (Finset.mem_univ i))
  intro f hf hfK i z hz
  exact (hder i f hf hfK z hz).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ i)) (by positivity))

theorem spanningCoronaDensity_compact_bound
    {b : ℕ} {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ}
    (hZ : ∀ k x i, DifferentiableOn ℂ
      (fun z => (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        Z k (cotangentChartInv x z)) i) (cotangentTarget x))
    (hspan : ∀ y, Submodule.span ℂ (Set.range (fun k => Z k y)) = ⊤)
    {K : Set (CotangentPoint M)} (hK : CotangentCompact K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (f : ℂ → CotangentPoint M), CotangentDisc f →
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, f z ∈ K) →
      ∀ i j z, z ∈ Metric.ball (0 : ℂ) 1 →
        ‖coronaDbarDensity (fun k w => spanningSigma G Z k (f w)) i j z‖ ^ 2 ≤
          A * (1 + ‖fderiv ℂ (fun w => G (f w)) z 1‖ ^ 2) := by
  obtain ⟨C, B, hC, hB, hnorm, hder⟩ := finite_cotangentCoefficient_disc_derivative_control
    hG (fun k x => spanningSigma_chart_contDiffOn hG hZ hspan x k) hK
  refine ⟨8 * B ^ 2 * C ^ 2, by positivity, fun f hf hfK i j z hz => ?_⟩
  have hbound (k : SpanningMinorIndex n q b) :
      ‖discDbarWithin (fun w => spanningSigma G Z k (f w)) z‖ ≤
        C * (‖fderiv ℂ (fun w => G (f w)) z 1‖ + 1) :=
    (discDbarWithin_norm_le _ hz).trans (hder f hf hfK k z hz)
  have h := coronaDbarDensity_norm_sq_le
    (σ := fun (k : SpanningMinorIndex n q b) w => spanningSigma G Z k (f w))
    (i := i) (j := j) (z := z) (B := B)
    (D := C * (‖fderiv ℂ (fun w => G (f w)) z 1‖ + 1)) hB
    (mul_nonneg hC (by positivity))
    (hnorm i _ (hfK z (Metric.ball_subset_closedBall hz)))
    (hnorm j _ (hfK z (Metric.ball_subset_closedBall hz))) (hbound i) (hbound j)
  refine h.trans ?_
  have hs : (‖fderiv ℂ (fun w => G (f w)) z 1‖ + 1) ^ 2 ≤
      2 * (1 + ‖fderiv ℂ (fun w => G (f w)) z 1‖ ^ 2) := by
    nlinarith [sq_nonneg (‖fderiv ℂ (fun w => G (f w)) z 1‖ - 1)]
  calc
    4 * B ^ 2 * (C * (‖fderiv ℂ (fun w => G (f w)) z 1‖ + 1)) ^ 2 =
        (4 * B ^ 2 * C ^ 2) * (‖fderiv ℂ (fun w => G (f w)) z 1‖ + 1) ^ 2 := by ring
    _ ≤ (4 * B ^ 2 * C ^ 2) *
        (2 * (1 + ‖fderiv ℂ (fun w => G (f w)) z 1‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

end Yau.Blueprint.V02Proof

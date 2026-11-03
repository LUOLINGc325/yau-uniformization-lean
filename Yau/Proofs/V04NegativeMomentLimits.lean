import Yau.Proofs.V04NegativeContinuity
import Yau.Proofs.V04NegativeTraceMoments
import Yau.Proofs.V04BoundaryAverages

/-! The actual first negative moment follows from the third by a free
threshold, with the sequential limit still inside the positive epsilon
limit. Circle averages are taken only after proving actual continuity. -/

open Filter MeasureTheory
open scoped Topology Matrix ComplexOrder MatrixOrder
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem circleAverage_mono_of_continuous {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hle : ∀ θ, f θ ≤ g θ) :
    circleAverage f ≤ circleAverage g := by
  apply mul_le_mul_of_nonneg_left
    (intervalIntegral.integral_mono_on (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _) (fun θ _ => hle θ))
  positivity

theorem circleAverage_const_add_div {f : ℝ → ℝ} (hf : Continuous f) (b c : ℝ) :
    circleAverage (fun θ => b + f θ / c) = b + circleAverage f / c := by
  unfold circleAverage
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((hf.intervalIntegrable _ _).div_const c), intervalIntegral.integral_const,
    intervalIntegral.integral_div]
  simp only [sub_zero, smul_eq_mul]
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hp, one_mul]
  ring

theorem negativeTrace_continuous_integrand {d : VariationData X q}
    (hd : VariationSetup d) {j a : ℕ} (ha : 4 ≤ a) {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) {E : ℂ → CotangentMatrix n}
    (hE : NormalizedDiscFrame d.G F.f E)
    (hT : ∀ θ, (boundarySymbol d j a F E (circlePoint θ)).IsHermitian) (p : ℕ) :
    Continuous (fun θ => (Matrix.trace
      (matrixNegative (boundarySymbol d j a F E (circlePoint θ)) ^ p)).re) :=
  matrixNegative_trace_pow_continuous
    (fun i k => (boundarySymbol_trace_contDiff hd j a ha F hF E hE i k).continuous) hT p

theorem negativeTrace_nonneg {d : VariationData X q}
    (j a : ℕ) (F : VariationDisc X) (E : ℂ → CotangentMatrix n) (p : ℕ) :
    0 ≤ negativeTrace d j a F E p := by
  unfold negativeTrace circleAverage
  apply mul_nonneg (by positivity)
  apply intervalIntegral.integral_nonneg (by positivity)
  intro θ _
  exact trace_negative_pow_nonneg _ p

theorem negativeTrace_one_le_cube {d : VariationData X q}
    (hd : VariationSetup d) {j a : ℕ} (ha : 4 ≤ a) {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) {E : ℂ → CotangentMatrix n}
    (hE : NormalizedDiscFrame d.G F.f E)
    (hT : ∀ θ, (boundarySymbol d j a F E (circlePoint θ)).IsHermitian)
    {τ : ℝ} (hτ : 0 < τ) :
    negativeTrace d j a F E 1 ≤ (2 * n : ℕ) * τ + negativeTrace d j a F E 3 / τ ^ 2 := by
  have h1 := negativeTrace_continuous_integrand hd ha hF hE hT 1
  have h3 := negativeTrace_continuous_integrand hd ha hF hE hT 3
  have hc : Continuous (fun θ => (2 * n : ℕ) * τ +
      (Matrix.trace (matrixNegative (boundarySymbol d j a F E (circlePoint θ)) ^ 3)).re / τ ^ 2) :=
    continuous_const.add (h3.div_const (τ ^ 2))
  have hle := circleAverage_mono_of_continuous h1 hc
    (fun θ => by simpa only [pow_one] using trace_negative_one_le_cube _ (hT θ) hτ)
  rw [circleAverage_const_add_div h3] at hle
  simpa only [negativeTrace] using hle

theorem negativeTrace_one_of_three {d : VariationData X q}
    (hd : VariationSetup d) {a : ℕ} (ha : 4 ≤ a) (hsymbol : SymbolBounds d a)
    (j : ℕ) (F : ℝ → ℕ → VariationDisc X) (E : ℝ → ℕ → ℂ → CotangentMatrix n)
    (hdata : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ν,
      AdmissibleVariationDisc d j (F ε ν) ∧ NormalizedDiscFrame d.G (F ε ν).f (E ε ν))
    (hthree : EpsSeqZero (fun ε ν => negativeTrace d j a (F ε ν) (E ε ν) 3)) :
    EpsSeqZero (fun ε ν => negativeTrace d j a (F ε ν) (E ε ν) 1) := by
  intro r hr
  let m : ℝ := (2 * n : ℕ)
  have hm : 0 ≤ m := by positivity
  let τ : ℝ := r / (2 * (m + 1))
  have hτ : 0 < τ := div_pos hr (by positivity)
  have hτsq : 0 < τ ^ 2 := sq_pos_of_pos hτ
  have hmτ : m * τ ≤ r / 2 := by
    have heq : 2 * (m + 1) * τ = r := by
      dsimp [τ]; field_simp
    nlinarith only [heq, hm, hτ.le]
  obtain ⟨CT, _, hT⟩ := hsymbol j
  filter_upwards [hdata, hthree (r / 2 * τ ^ 2) (mul_pos (half_pos hr) hτsq)]
    with ε hε hεthree
  filter_upwards [hεthree] with ν hν
  have hle := negativeTrace_one_le_cube hd ha (hε ν).1 (hε ν).2
    (fun θ => ((hT _ _ (hε ν).1 (hε ν).2).1 θ).1) hτ
  have hc : negativeTrace d j a (F ε ν) (E ε ν) 3 / τ ^ 2 ≤ r / 2 := by
    apply (div_le_iff₀ hτsq).2
    exact (le_abs_self _).trans hν
  rw [abs_of_nonneg (negativeTrace_nonneg _ _ _ _ 1)]
  change negativeTrace d j a (F ε ν) (E ε ν) 1 ≤ r
  change negativeTrace d j a (F ε ν) (E ε ν) 1 ≤ m * τ +
    negativeTrace d j a (F ε ν) (E ε ν) 3 / τ ^ 2 at hle
  linarith only [hle, hmτ, hc]

end Yau.Blueprint.V04Proof

import Yau.Proofs.V02CoronaDensityEnergy
import Yau.Proofs.V02CircleQuadratic

/-! The actual matrix of canonical corona corrections is a smooth periodic
finite vector with a single uniform L² and Fourier bound. -/

open scoped Topology ContDiff Manifold Matrix
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

theorem parameterAverage_finsetSum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ s, Continuous (f i)) :
    circleAverage (fun θ => ∑ i ∈ s, f i θ) = ∑ i ∈ s, circleAverage (f i) := by
  unfold circleAverage
  rw [intervalIntegral.integral_finsetSum (fun i hi => (hf i hi).intervalIntegrable _ _),
    Finset.mul_sum]

variable {n q b : ℕ} {M : ComplexManifold n}

def spanningCorrectionTrace (G : CotangentPoint M → ComplexVector q)
    (Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ)
    (f : ℂ → CotangentPoint M) (θ : ℝ)
    (p : SpanningMinorIndex n q b × SpanningMinorIndex n q b) : ℂ :=
  coronaDbarCorrection (fun k w => spanningSigma G Z k (f w)) p.1 p.2 (circlePoint θ)

theorem spanningCorrectionTrace_contDiff
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ}
    (hZ : ∀ k x i, DifferentiableOn ℂ
      (fun z => (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        Z k (cotangentChartInv x z)) i) (cotangentTarget x))
    (hspan : ∀ y, Submodule.span ℂ (Set.range (fun k => Z k y)) = ⊤)
    {f : ℂ → CotangentPoint M} (hf : CotangentDisc f)
    (p : SpanningMinorIndex n q b × SpanningMinorIndex n q b) :
    ContDiff ℝ ∞ (fun θ => spanningCorrectionTrace G Z f θ p) := by
  apply contDiffOn_univ.mp
  exact (coronaDbarCorrection_contDiffOn
    (fun k => spanningSigma_disc_contDiffOn hG hZ hspan hf k) p.1 p.2).comp
    V03Proof.circlePoint_contDiff.contDiffOn (fun θ _ => V03Proof.circlePoint_mem_closedBall θ)

theorem spanningCorrectionTrace_periodic
    (G : CotangentPoint M → ComplexVector q)
    (Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ)
    (f : ℂ → CotangentPoint M)
    (p : SpanningMinorIndex n q b × SpanningMinorIndex n q b) :
    Function.Periodic (fun θ => spanningCorrectionTrace G Z f θ p) (2 * Real.pi) := by
  intro θ
  exact congrArg (coronaDbarCorrection (fun k w => spanningSigma G Z k (f w)) p.1 p.2)
    (V03Proof.circlePoint_periodic θ)

theorem spanningCorrectionTrace_uniform_bound
    {X : KahlerManifold n} {d : VariationData X q} (hd : VariationSetup d)
    {Z : Fin b → CotangentPoint X.manifold → CotangentIndex n → ℂ}
    (hZ : ∀ k x i, DifferentiableOn ℂ
      (fun z => (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        Z k (cotangentChartInv x z)) i) (cotangentTarget x))
    (hspan : ∀ y, Submodule.span ℂ (Set.range (fun k => Z k y)) = ⊤)
    {K : Set (CotangentPoint X.manifold)} (hK : CotangentCompact K) (E₀ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (j : ℕ) (F : VariationDisc X),
      AdmissibleVariationDisc d j F → (variationEnergy d j F).toReal ≤ E₀ →
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, F.f z ∈ K) →
      circleAverage (fun θ => ∑ p, ‖spanningCorrectionTrace d.G Z F.f θ p‖ ^ 2) ≤ B ∧
        boundaryDSq (spanningCorrectionTrace d.G Z F.f) ≤ ENNReal.ofReal B := by
  classical
  let ι := SpanningMinorIndex n q b × SpanningMinorIndex n q b
  obtain ⟨B₀, hB₀, hbound⟩ := spanningCoronaCorrection_uniform_trace hd hZ hspan hK E₀
  let B : ℝ := (Fintype.card ι : ℝ) * B₀
  refine ⟨B, mul_nonneg (Nat.cast_nonneg _) hB₀, fun j F hF hE hfK => ?_⟩
  have hc (p : ι) := (spanningCorrectionTrace_contDiff hd.2.2.2.2.1 hZ hspan hF.1 p).continuous
  have heach (p : ι) := hbound j F hF hE hfK p.1 p.2
  have hmean (p : ι) : circleAverage
      (fun θ => ‖spanningCorrectionTrace d.G Z F.f θ p‖ ^ 2) ≤ B₀ := by
    apply (ENNReal.ofReal_le_ofReal_iff hB₀).mp
    exact (le_add_right le_rfl).trans (heach p)
  have hD (p : ι) : boundaryDSq
      (fun θ (_ : Unit) => spanningCorrectionTrace d.G Z F.f θ p) ≤ ENNReal.ofReal B₀ :=
    (le_add_left le_rfl).trans (heach p)
  constructor
  · rw [parameterAverage_finsetSum (f := fun (p : ι) θ =>
      ‖spanningCorrectionTrace d.G Z F.f θ p‖ ^ 2) Finset.univ (fun p _ => (hc p).norm.pow 2)]
    have hh := Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) => hmean p)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hh
  rw [V03Proof.boundaryDSq_eq_sum_singleton]
  calc
    _ ≤ ∑ p : ι, ENNReal.ofReal B₀ := Finset.sum_le_sum (fun p _ => hD p)
    _ = ENNReal.ofReal B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, B,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

end Yau.Blueprint.V02Proof

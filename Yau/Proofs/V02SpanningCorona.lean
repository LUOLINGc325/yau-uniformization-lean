import Yau.Proofs.V02CoronaSolution
import Yau.Proofs.V02SpanningDisc

/-! The original global spanning fields give actual holomorphic corona
coefficients along each arbitrary smooth cotangent disc. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

variable {n q b : ℕ} {M : ComplexManifold n}

def spanningCorona (G : CotangentPoint M → ComplexVector q)
    (Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ)
    (f : ℂ → CotangentPoint M) (k : SpanningMinorIndex n q b) : ℂ → ℂ :=
  coronaSolution (fun k ζ => spanningMinor G Z k (f ζ))
    (fun k ζ => spanningSigma G Z k (f ζ)) k

theorem spanningCorona_contDiffOn
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ}
    (hZ : ∀ k x i, DifferentiableOn ℂ
      (fun z => (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        Z k (cotangentChartInv x z)) i) (cotangentTarget x))
    (hspan : ∀ y, Submodule.span ℂ (Set.range (fun k => Z k y)) = ⊤)
    {f : ℂ → CotangentPoint M} (hf : CotangentDisc f) (k : SpanningMinorIndex n q b) :
    ContDiffOn ℂ ∞ (spanningCorona G Z f k) (Metric.closedBall (0 : ℂ) 1) :=
  coronaSolution_complex_contDiffOn
    (fun k => spanningMinor_disc_contDiffOn hG.1 hZ hf k)
    (fun k => spanningSigma_disc_contDiffOn hG hZ hspan hf k)
    (fun ζ _ => spanningSigma_sum_eq_one hG hspan (f ζ)) k

theorem spanningCorona_sum_eq_one
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ}
    (hZ : ∀ k x i, DifferentiableOn ℂ
      (fun z => (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        Z k (cotangentChartInv x z)) i) (cotangentTarget x))
    (hspan : ∀ y, Submodule.span ℂ (Set.range (fun k => Z k y)) = ⊤)
    {f : ℂ → CotangentPoint M} (hf : CotangentDisc f)
    {ζ : ℂ} (hζ : ζ ∈ Metric.closedBall (0 : ℂ) 1) :
    ∑ k : SpanningMinorIndex n q b, spanningCorona G Z f k ζ * spanningMinor G Z k (f ζ) = 1 :=
  coronaSolution_sum_eq_one
    (fun k => spanningSigma_disc_contDiffOn hG hZ hspan hf k)
    (fun ζ _ => spanningSigma_sum_eq_one hG hspan (f ζ)) hζ

end Yau.Blueprint.V02Proof

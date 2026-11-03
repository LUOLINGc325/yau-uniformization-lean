import Yau.Proofs.V02SpanningSmooth

/-! The actual normalized conjugate minors used for the corona correction.
Their common denominator is strictly positive; no individual minor is inverted. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Finset

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

abbrev SpanningMinorIndex (n q b : ℕ) :=
  (CotangentIndex n → Fin q) × (CotangentIndex n → Fin b)

variable {n q b : ℕ} {M : ComplexManifold n}

def spanningMinor (G : CotangentPoint M → ComplexVector q)
    (Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ)
    (k : SpanningMinorIndex n q b) (y : CotangentPoint M) : ℂ :=
  ((spanningAmbientMatrix G Z y).submatrix k.1 k.2).det

def spanningSigma (G : CotangentPoint M → ComplexVector q)
    (Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ)
    (k : SpanningMinorIndex n q b) (y : CotangentPoint M) : ℂ :=
  star (spanningMinor G Z k y) / (spanningMinorSq G Z y : ℂ)

theorem sum_spanningMinor_norm_sq (G : CotangentPoint M → ComplexVector q)
    (Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ) (y : CotangentPoint M) :
    ∑ k : SpanningMinorIndex n q b, ‖spanningMinor G Z k y‖ ^ 2 =
      spanningMinorSq G Z y := by
  simp only [Fintype.sum_prod_type, spanningMinor, spanningAmbientMatrix,
    spanningMinorSq, tupleMinorSq]

theorem spanningSigma_sum_eq_one {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G)
    {Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ}
    (hZ : ∀ y, Submodule.span ℂ (Set.range (fun k => Z k y)) = ⊤)
    (y : CotangentPoint M) :
    ∑ k : SpanningMinorIndex n q b, spanningSigma G Z k y * spanningMinor G Z k y = 1 := by
  have hS : (spanningMinorSq G Z y : ℂ) ≠ 0 := by
    exact_mod_cast (spanningMinorSq_pos hG hZ y).ne'
  simp only [spanningSigma, div_mul_eq_mul_div, V03Proof.star_mul_self_eq_norm_sq]
  rw [← Finset.sum_div, ← Complex.ofReal_sum, sum_spanningMinor_norm_sq,
    div_self hS]

theorem spanningSigma_chart_contDiffOn
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ}
    (hZ : ∀ k x i, DifferentiableOn ℂ
      (fun z => (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        Z k (cotangentChartInv x z)) i) (cotangentTarget x))
    (hspan : ∀ y, Submodule.span ℂ (Set.range (fun k => Z k y)) = ⊤)
    (x : M.Carrier) (k : SpanningMinorIndex n q b) :
    ContDiffOn ℝ ∞ (fun z => spanningSigma G Z k (cotangentChartInv x z))
      (cotangentTarget x) := by
  have hm := (spanning_minor_chart_contDiffOn hG.1 hZ x k.1 k.2).restrict_scalars ℝ
  have hS := Complex.ofRealCLM.contDiff.comp_contDiffOn
    (spanningMinorSq_chart_contDiffOn hG.1 hZ x)
  change ContDiffOn ℝ ∞ (fun z => star (spanningMinor G Z k (cotangentChartInv x z)) *
    (spanningMinorSq G Z (cotangentChartInv x z) : ℂ)⁻¹) (cotangentTarget x)
  exact (Complex.conjCLE.contDiff.comp_contDiffOn hm).mul (hS.inv (fun z _ => by
    change (spanningMinorSq G Z (cotangentChartInv x z) : ℂ) ≠ 0
    exact_mod_cast (spanningMinorSq_pos hG hspan (cotangentChartInv x z)).ne'))

end Yau.Blueprint.V02Proof

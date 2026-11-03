import Yau.Proofs.F01RestrictedGram
import Yau.Proofs.F01RescaledDifferential
import Yau.Proofs.F01ConformalMetric

/-! Exact Gram identities for actual restricted and rescaled charts. -/
open Set
open scoped Manifold ContDiff
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem chartGramCoefficient_conformalField (g : HermitianField M) (f : M.Carrier → ℝ)
    (e : ComplexVector n → M.Carrier) (z : ComplexVector n) (i j : Fin n) :
    chartGramCoefficient (conformalField g f) e z i j =
      (Real.exp (f (e z)) : ℂ) * chartGramCoefficient g e z i j := rfl

theorem chartGramCoefficient_rescaled (g : HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e e.source)
    (z₀ : ComplexVector n) (a : ℂ) (ha : a ≠ 0) {z : ComplexVector n}
    (hz : z ∈ (rescaledChart e z₀ a ha).source) (i j : Fin n) :
    chartGramCoefficient g (rescaledChart e z₀ a ha) z i j =
      (star a * a) * chartGramCoefficient g e (z₀ + a • z) i j := by
  have hi := rescaledChart_mfderiv_apply e he z₀ a ha hz (stdVec i)
  have hj := rescaledChart_mfderiv_apply e he z₀ a ha hz (stdVec j)
  change (g (e (z₀ + a • z))).toFun _ _ = _
  exact (congrArg₂ (g (e (z₀ + a • z))).toFun hi hj).trans (by
    rw [HermitianInnerProduct.map_smul_left, HermitianInnerProduct.map_smul_right]
    unfold chartGramCoefficient
    ring)

theorem chartGramCoefficient_rescaled_real (g : HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e e.source)
    (z₀ : ComplexVector n) (s : ℝ) (hs : (s : ℂ) ≠ 0) {z : ComplexVector n}
    (hz : z ∈ (rescaledChart e z₀ (s : ℂ) hs).source) (i j : Fin n) :
    chartGramCoefficient g (rescaledChart e z₀ (s : ℂ) hs) z i j =
      ((s ^ 2 : ℝ) : ℂ) * chartGramCoefficient g e (z₀ + s • z) i j := by
  have h := chartGramCoefficient_rescaled g e he z₀ (s : ℂ) hs hz i j
  simpa only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← pow_two,
    ← Complex.ofReal_pow,
    Complex.coe_smul] using h

end Yau.NodeProofs.F01Aux

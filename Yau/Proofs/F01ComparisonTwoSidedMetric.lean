import Yau.Proofs.F01ComparisonLogDetLower
import Yau.Proofs.F01LogDetMetricLower

/-! The genuine comparison Q and the genuine upper metric estimate yield
both metric orders and the scalar bounds needed for uniform parabolicity. -/
noncomputable section
open Set
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem two_sided_metric_of_nonnegative_comparison
    (α : HermitianField M) (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ)
    (φ : M.Carrier → ℝ) {T D B Mφ : ℝ}
    (hT : 0 ≤ T) (hD : 0 < D) (hhalf : 2 * T ≤ D)
    (hB : 0 ≤ B) (hMφ : 0 ≤ Mφ)
    (hU0 : ∀ x, U x 0 = 0)
    (hpde : ∀ x s, s ∈ Icc 0 T →
      HasDerivWithinAt (U x) (flowLogDetRatio α h x s) (Icc 0 T) s)
    (horder : ∀ x s, s ∈ Icc 0 T →
      ((Real.exp B : ℂ) • gMat α x - gMat (h s) x).PosSemidef)
    (hφ : ∀ x, -Mφ ≤ φ x)
    (hQ : ∀ x s, s ∈ Icc 0 T →
      0 ≤ comparisonFunction D n U (flowLogDetRatio α h) φ x s) :
    let A := 2 * Mφ + (n : ℝ) * B + n
    ∀ x t, t ∈ Icc 0 T →
      (gMat (h t) x - (Real.exp (-(A + (n : ℝ) * B)) : ℂ) • gMat α x).PosSemidef ∧
      ((Real.exp B : ℂ) • gMat α x - gMat (h t) x).PosSemidef ∧
      |flowLogDetRatio α h x t| ≤ A ∧ |U x t| ≤ A * t := by
  dsimp only
  have hscalar := scalar_abs_bounds_of_nonnegative_comparison α h U φ hT hD hhalf hB hMφ
    hU0 hpde horder hφ hQ
  intro x t ht
  exact ⟨flow_metric_exp_lower_of_logdet α h hB x t (horder x t ht)
    (abs_le.mp (hscalar x t ht).1).1, horder x t ht, hscalar x t ht⟩

end Yau.NodeProofs.F01Aux

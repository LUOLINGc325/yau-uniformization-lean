import Yau.Proofs.F03WeightBasic

/-! Closed-slab regularity of the actual polynomial-exponential weight. -/

noncomputable section
open scoped Manifold Topology ContDiff
open MeasureTheory Filter

namespace Yau.Proofs.F03Aux
open Yau Blueprint

variable {n : ℕ} {M : ComplexManifold n}

theorem comparisonWeight_smoothSpaceC1Time (u : M.Carrier → ℝ)
    (hu : SmoothFn u) (hu0 : ∀ x, 0 < u x) (H : M.Carrier → ℝ → ℝ)
    {I : Set ℝ} (hH : SmoothSpaceC1Time H I) (A : ℝ) (k : ℕ) :
    SmoothSpaceC1Time (comparisonWeight u H A k) I := by
  constructor
  · intro t ht a
    simp only [comparisonWeight, zpow_neg, zpow_natCast]
    exact (((hu a).pow k).inv (fun z _ => pow_ne_zero _ (hu0 _).ne')).mul
      (((contDiffOn_const.mul (hH.1 t ht a)).div ((hu a).pow 2)
        (fun z _ => pow_ne_zero _ (hu0 _).ne')).exp)
  · intro a
    have huj : ContDiffOn ℝ 1
        (fun p : ComplexVector n × ℝ => u (chartInv a p.1)) (chartTarget a ×ˢ I) :=
      ((hu a).comp contDiffOn_fst (fun p hp => hp.1)).of_le (by simp)
    simp only [comparisonWeight, zpow_neg, zpow_natCast]
    exact ((huj.pow k).inv (fun p _ => pow_ne_zero _ (hu0 _).ne')).mul
      (((contDiffOn_const.mul (hH.2 a)).div (huj.pow 2)
        (fun p _ => pow_ne_zero _ (hu0 _).ne')).exp)

/-- The time coefficient in the F03 contract is integrable across zero
for every strictly positive beta, including beta below one. -/
theorem cutoff_timeCoefficient_intervalIntegrable {β T : ℝ} (hβ : 0 < β) :
    IntervalIntegrable (fun t : ℝ => 1 + t ^ (β - 1)) volume 0 T := by
  apply intervalIntegrable_const.add
  exact intervalIntegral.intervalIntegrable_rpow' (by linarith)

end Yau.Proofs.F03Aux

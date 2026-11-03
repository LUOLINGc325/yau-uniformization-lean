import Yau.Proofs.P03TranslatedTests

open scoped Topology ContDiff
open MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ}

/-- Interior mollifications satisfy the genuine complex Fréchet equation,
using precisely the original nonconjugated scalar weak tests. -/
theorem interior_smoothing_holomorphic
    {u k : ComplexVector n → ℂ} {a : ComplexVector n} {r : ℝ}
    {U : Set (ComplexVector n)} (hKU : Metric.closedBall a (4 * r) ⊆ U)
    (huK : MemLp u 2 ((volume : Measure (ComplexVector n)).restrict
      (Metric.closedBall a (4 * r))))
    (hweak : ∀ (i : Fin n) (ψ : ComplexVector n → ℂ),
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ y, u y * wirtBar ψ y (stdVec i)) = 0)
    (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k)
    (hks : tsupport k ⊆ Metric.closedBall 0 r) :
    DifferentiableOn ℂ
      (cmulConv ((Metric.closedBall a (4 * r)).indicator u) k)
      (Metric.ball a (3 * r)) := by
  let K := Metric.closedBall a (4 * r)
  let f := K.indicator u
  have hf : Integrable f volume :=
    integrable_indicator_of_compact_memLp K (isCompact_closedBall _ _) huK
  intro x hx
  apply DifferentiableAt.differentiableWithinAt
  apply differentiableAt_complex_of_wirtBar_basis_zero
    ((cmulConv_contDiff hf hk hkc).differentiable (by simp) x)
  intro i
  let ψ : ComplexVector n → ℂ := fun y => k (x - y)
  have hsK : tsupport ψ ⊆ K := translatedKernel_inner_support hks hx
  have ht := hweak i ψ (translatedKernel_contDiff hk x)
    (translatedKernel_hasCompactSupport hkc x) (hsK.trans hKU)
  have hcut : (∫ y, f y * wirtBar ψ y (stdVec i)) = 0 := by
    calc
      (∫ y, f y * wirtBar ψ y (stdVec i)) =
          ∫ y, u y * wirtBar ψ y (stdVec i) := by
        apply integral_congr_ae
        filter_upwards with y
        exact indicator_mul_wirtBar_eq_of_tsupport_subset hsK y (stdVec i)
      _ = 0 := ht
  have hneg : -(∫ y, f y * wirtBar k (x - y) (stdVec i)) = 0 := by
    simpa only [ψ, wirtBar_translatedKernel hk, mul_neg, integral_neg] using hcut
  rw [wirtBar_cmulConv hf hk hkc x (stdVec i)]
  exact neg_eq_zero.mp hneg

end Yau.NodeProofs.P03Aux

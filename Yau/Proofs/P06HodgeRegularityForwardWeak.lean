import Yau.Proofs.P06HodgeRegularityTranspose
import Yau.Proofs.P06HodgeRegularityTestAlgebra

/-! The natural LOCAL forward distributional PDE uses only tests compactly
supported inside its region. No output regularity is stored in the predicate. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux

variable {E ι α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Fintype ι] [Fintype α]

theorem regularityForwardTranspose_test
    (v : ι → E) (a : α → α → ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c))
    {O : Set E} {φ : E → ℝ} (hφ : regularityTest O φ) (r c : α) :
    regularityTest O (fun z => regularityForwardTranspose v a e1 e0 φ z r c) := by
  unfold regularityForwardTranspose
  apply regularityTest_add
  · apply regularityTest_sub
    · apply regularityTest_neg
      apply regularityTest_sum
      intro i
      apply regularityTest_sum
      intro j
      exact regularityTest_direction
        (regularityTest_direction (regularityTest_coeff_mul hφ (ha r c i j)) (v i)) (v j)
    · apply regularityTest_sum
      intro i
      exact regularityTest_direction (regularityTest_coeff_mul hφ (he1 r c i)) (v i)
  · exact regularityTest_coeff_mul hφ (he0 r c)

def regularityForwardWeak [DecidableEq α] (ν : Measure E) (O : Set E) (v : ι → E)
    (q : ι → ι → E → ℝ) (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (U W : E → α → ℝ) : Prop :=
  ∀ r φ, regularityTest O φ →
    (∫ z, ∑ c, regularityForwardTranspose v (regularityScalarSystemA q) e1 e0 φ z r c * U z c
      ∂ν.restrict O) = ∫ z, φ z * W z r ∂ν.restrict O

end Yau.NodeProofs.P06Aux

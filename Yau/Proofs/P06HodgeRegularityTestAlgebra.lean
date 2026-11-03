import Yau.Proofs.P06HodgeRegularityCalculus

/-! Supported-test linear algebra, with actual compact smooth functions. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]

theorem regularityTest_neg {O : Set E} {φ : E → ℝ} (hφ : regularityTest O φ) :
    regularityTest O (fun z => -φ z) :=
  (regularityTestSpace O).neg_mem hφ

theorem regularityTest_add {O : Set E} {φ ψ : E → ℝ}
    (hφ : regularityTest O φ) (hψ : regularityTest O ψ) :
    regularityTest O (fun z => φ z + ψ z) :=
  (regularityTestSpace O).add_mem hφ hψ

theorem regularityTest_sub {O : Set E} {φ ψ : E → ℝ}
    (hφ : regularityTest O φ) (hψ : regularityTest O ψ) :
    regularityTest O (fun z => φ z - ψ z) :=
  (regularityTestSpace O).sub_mem hφ hψ

theorem regularityTest_sum {γ : Type*} [Fintype γ] {O : Set E} (F : γ → E → ℝ)
    (hF : ∀ c, regularityTest O (F c)) :
    regularityTest O (fun z => ∑ c, F c z) := by
  classical
  have h : (∑ c, F c) ∈ regularityTestSpace O :=
    (regularityTestSpace O).sum_mem (fun c _ => hF c)
  have hfun : (fun z => ∑ c, F c z) = ∑ c, F c := by
    funext z
    simp only [Finset.sum_apply]
  rw [hfun]
  exact h

theorem regularityTest_coeff_mul {O : Set E} {φ a : E → ℝ}
    (hφ : regularityTest O φ) (ha : ContDiff ℝ ∞ a) :
    regularityTest O (fun z => a z * φ z) := by
  have hfun : (fun z => a z * φ z) = fun z => φ z * a z := funext (fun _ => mul_comm _ _)
  rw [hfun]
  exact regularityTest_mul hφ ha

end Yau.NodeProofs.P06Aux

import Yau.Proofs.P06HodgeRegularityWordCalculus

/-! A finite smooth-test word operator and its exact coefficient commutator. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux

variable {E ι γ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype γ]

def regularityWordOperator (v : ι → E) (a : γ → E → ℝ) (words : γ → List ι)
    (φ : E → ℝ) (z : E) : ℝ :=
  ∑ c, regularityCoefficientWord v (words c) (fun y => a c y * φ y) z

theorem regularityWordOperator_contDiff
    (v : ι → E) (a : γ → E → ℝ) (words : γ → List ι)
    (ha : ∀ c, ContDiff ℝ ∞ (a c)) {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (regularityWordOperator v a words φ) :=
  ContDiff.sum fun c _ => regularityCoefficientWord_contDiff v ((ha c).mul hφ) (words c)

theorem regularityWordOperator_derivative
    (v : ι → E) (a : γ → E → ℝ) (words : γ → List ι)
    (ha : ∀ c, ContDiff ℝ ∞ (a c)) {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (ell : ι) :
    regularityDirection (v ell) (regularityWordOperator v a words φ) =
      fun z => regularityWordOperator v (fun c => regularityDirection (v ell) (a c)) words φ z +
        regularityWordOperator v a words (regularityDirection (v ell) φ) z := by
  unfold regularityWordOperator
  rw [regularityDirection_sum _
    (fun c => regularityCoefficientWord_contDiff v ((ha c).mul hφ) (words c)) (v ell)]
  funext z
  simp_rw [regularityCoefficientWord_mul_commutator v (ha _) hφ]
  exact Finset.sum_add_distrib

end Yau.NodeProofs.P06Aux

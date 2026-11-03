import Yau.Proofs.P06HodgeRegularityLeibnizWords

/-! True smooth word calculus for the transpose prolongation commutator. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem regularityCoefficientWord_contDiff (v : ι → E) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (w : List ι) : ContDiff ℝ ∞ (regularityCoefficientWord v w f) := by
  induction w with
  | nil => exact hf
  | cons i w ih => exact regularityDirection_contDiff ih (v i)

theorem regularityCoefficientWord_add (v : ι → E) {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (w : List ι) :
    regularityCoefficientWord v w (fun z => f z + g z) =
      fun z => regularityCoefficientWord v w f z + regularityCoefficientWord v w g z := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change regularityDirection (v i) (regularityCoefficientWord v w (fun z => f z + g z)) = _
    rw [ih, regularityDirection_add (regularityCoefficientWord_contDiff v hf w)
      (regularityCoefficientWord_contDiff v hg w) (v i)]
    rfl

theorem regularityCoefficientWord_commute_direction (v : ι → E) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (w : List ι) (ell : ι) :
    regularityDirection (v ell) (regularityCoefficientWord v w f) =
      regularityCoefficientWord v w (regularityDirection (v ell) f) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change regularityDirection (v ell) (regularityDirection (v i) (regularityCoefficientWord v w f)) = _
    rw [regularityDirection_commute (regularityCoefficientWord_contDiff v hf w) (v ell) (v i), ih]
    rfl

/-- The full variable-coefficient commutator is an identity on actual
smooth compact tests. It differentiates no raw weak field. -/
theorem regularityCoefficientWord_mul_commutator (v : ι → E) {a φ : E → ℝ}
    (ha : ContDiff ℝ ∞ a) (hφ : ContDiff ℝ ∞ φ) (w : List ι) (ell : ι) :
    regularityDirection (v ell) (regularityCoefficientWord v w (fun z => a z * φ z)) =
      fun z => regularityCoefficientWord v w
        (fun y => regularityDirection (v ell) a y * φ y) z +
      regularityCoefficientWord v w (fun y => a y * regularityDirection (v ell) φ y) z := by
  rw [regularityCoefficientWord_commute_direction v (ha.mul hφ) w ell,
    regularityDirection_mul ha hφ (v ell), regularityCoefficientWord_add v
      ((regularityDirection_contDiff ha (v ell)).mul hφ)
      (ha.mul (regularityDirection_contDiff hφ (v ell))) w]

end Yau.NodeProofs.P06Aux

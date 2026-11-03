import Yau.LeafProofs.L18
import Yau.LeafProofs.L16WeakToClassical

/-! Actual local directional jets and their compact-test adjoints. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau Parabolic LeafProofs.L18Aux LeafProofs.L16Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- Arbitrary real directions act outermost at the head of the word. -/
def directionalWordDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) : List E → E → ℝ
  | [] => f
  | v :: w => fun x => fderiv ℝ (directionalWordDerivative f w) x v

theorem directionalWordDerivative_append {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (a b : List E) :
    directionalWordDerivative f (a++b) = directionalWordDerivative (directionalWordDerivative f b) a := by
  induction a with
  | nil => rfl
  | cons v a ih => simp only [List.cons_append,directionalWordDerivative,ih]

theorem directionalWordDerivative_contDiffOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {O : Set E} (hO : IsOpen O)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (w : List E) :
    ContDiffOn ℝ ∞ (directionalWordDerivative f w) O := by
  induction w with
  | nil => exact hf
  | cons v w ih =>
    exact (ih.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const

theorem directionalWordDerivative_eventuallyEq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f k : E → ℝ} {x : E}
    (h : f =ᶠ[𝓝 x] k) (w : List E) :
    directionalWordDerivative f w =ᶠ[𝓝 x] directionalWordDerivative k w := by
  induction w with
  | nil => exact h
  | cons v w ih =>
    have hd : fderiv ℝ (directionalWordDerivative f w) =ᶠ[𝓝 x]
        fderiv ℝ (directionalWordDerivative k w) := ih.fderiv
    filter_upwards [hd] with y hy
    exact congrArg (fun L : E →L[ℝ] ℝ => L v) hy

theorem test_directionalWordDerivative {n : ℕ} {Q : Set (Point n)}
    {φ : Point n → ℝ} (hφ : Test Q φ) (w : List (Point n)) :
    Test Q (directionalWordDerivative φ w) := by
  induction w with
  | nil => exact hφ
  | cons v w ih => exact test_directionalDerivative ih v

/-- Repeated actual integration by parts shifts every finite local jet
onto the reversed derivative word of a genuine compact smooth test. -/
theorem directionalWordDerivative_test_integral {n : ℕ} {Q : Set (Point n)}
    (hQ : IsOpen Q) {f : Point n → ℝ} (hf : ContDiffOn ℝ ∞ f Q)
    (w : List (Point n)) {φ : Point n → ℝ} (hφ : Test Q φ) :
    (∫ p, directionalWordDerivative f w p * φ p) =
      (-1 : ℝ) ^ w.length * ∫ p, f p * directionalWordDerivative φ w.reverse p := by
  induction w generalizing φ with
  | nil => simp only [directionalWordDerivative,List.reverse_nil,List.length_nil,pow_zero,one_mul]
  | cons v w ih =>
    have hφv := test_directionalDerivative hφ v
    have hIBP := integral_compactTest_direction_on (volume : Measure (Point n)) hQ
      (hφ.1.of_le (by simp)) hφ.2.1 hφ.2.2
      ((directionalWordDerivative_contDiffOn hQ hf w).of_le (by simp)) v
    have hStep : (∫ p, directionalWordDerivative f (v::w) p * φ p) =
        -(∫ p, directionalWordDerivative f w p * fderiv ℝ φ p v) := by
      convert hIBP using 1
      · congr 1
        funext p
        simp only [directionalWordDerivative,mul_comm]
      · congr 2
        funext p
        exact mul_comm _ _
    rw [hStep,ih hφv]
    have heq : directionalWordDerivative (fun p => fderiv ℝ φ p v) w.reverse =
        directionalWordDerivative φ (v::w).reverse := by
      simp only [List.reverse_cons,directionalWordDerivative_append,directionalWordDerivative]
    rw [heq]
    simp only [List.length_cons,pow_succ]
    ring

end Yau.Proofs.F03Aux

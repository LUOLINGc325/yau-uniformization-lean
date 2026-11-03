import Yau.Proofs.E02PolynomialJet
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! V01 scratch source: the penalty is a smooth sum of three squares,
rather than the square of the product's maximum norm. -/

noncomputable section

open Set Filter Asymptotics
open scoped Topology ContDiff Asymptotics

namespace Yau.Blueprint.V01Proof

open Yau.NodeProofs.E02Aux

variable {n : ℕ}

def coordinateSquare (a p : ComplexVector n × ComplexVector n × ℝ) : ℝ :=
  ‖p.1 - a.1‖ ^ 2 + ‖p.2.1 - a.2.1‖ ^ 2 + (p.2.2 - a.2.2) ^ 2

theorem coordinateSquare_nonneg (a p : ComplexVector n × ComplexVector n × ℝ) :
    0 ≤ coordinateSquare a p := by
  unfold coordinateSquare
  positivity

@[simp] theorem coordinateSquare_self (a : ComplexVector n × ComplexVector n × ℝ) :
    coordinateSquare a a = 0 := by
  simp [coordinateSquare]

theorem coordinateSquare_eq_zero_iff (a p : ComplexVector n × ComplexVector n × ℝ) :
    coordinateSquare a p = 0 ↔ p = a := by
  constructor
  · intro hp
    have h₁ : ‖p.1 - a.1‖ = 0 := by
      have := sq_nonneg ‖p.2.1 - a.2.1‖
      have := sq_nonneg (p.2.2 - a.2.2)
      dsimp [coordinateSquare] at hp
      nlinarith [sq_nonneg ‖p.1 - a.1‖]
    have h₂ : ‖p.2.1 - a.2.1‖ = 0 := by
      have := sq_nonneg ‖p.1 - a.1‖
      have := sq_nonneg (p.2.2 - a.2.2)
      dsimp [coordinateSquare] at hp
      nlinarith [sq_nonneg ‖p.2.1 - a.2.1‖]
    have h₃ : p.2.2 - a.2.2 = 0 := by
      dsimp [coordinateSquare] at hp
      nlinarith [sq_nonneg ‖p.1 - a.1‖, sq_nonneg ‖p.2.1 - a.2.1‖]
    exact Prod.ext (sub_eq_zero.mp (norm_eq_zero.mp h₁))
      (Prod.ext (sub_eq_zero.mp (norm_eq_zero.mp h₂)) (sub_eq_zero.mp h₃))
  · rintro rfl
    simp [coordinateSquare]

theorem norm_sub_sq_le_coordinateSquare (a p : ComplexVector n × ComplexVector n × ℝ) :
    ‖p - a‖ ^ 2 ≤ coordinateSquare a p := by
  simp only [coordinateSquare, Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
  rcases le_total ‖p.2.1 - a.2.1‖ |p.2.2 - a.2.2| with hbc | hcb
  · rw [max_eq_right hbc]
    rcases le_total ‖p.1 - a.1‖ |p.2.2 - a.2.2| with hac | hca
    · rw [max_eq_right hac, sq_abs]
      nlinarith [sq_nonneg ‖p.1 - a.1‖, sq_nonneg ‖p.2.1 - a.2.1‖]
    · rw [max_eq_left hca]
      nlinarith [sq_nonneg ‖p.2.1 - a.2.1‖, sq_nonneg (p.2.2 - a.2.2)]
  · rw [max_eq_left hcb]
    rcases le_total ‖p.1 - a.1‖ ‖p.2.1 - a.2.1‖ with hab | hba
    · rw [max_eq_right hab]
      nlinarith [sq_nonneg ‖p.1 - a.1‖, sq_nonneg (p.2.2 - a.2.2)]
    · rw [max_eq_left hba]
      nlinarith [sq_nonneg ‖p.2.1 - a.2.1‖, sq_nonneg (p.2.2 - a.2.2)]

theorem coordinateSquare_contDiff (a : ComplexVector n × ComplexVector n × ℝ) :
    ContDiff ℝ ∞ (coordinateSquare a) := by
  have h₁ : ContDiff ℝ ∞ (fun p : ComplexVector n × ComplexVector n × ℝ => p.1 - a.1) := by
    fun_prop
  have h₂ : ContDiff ℝ ∞ (fun p : ComplexVector n × ComplexVector n × ℝ => p.2.1 - a.2.1) := by
    fun_prop
  exact ((h₁.norm_sq ℂ).add (h₂.norm_sq ℂ)).add (by fun_prop)

def quadraticSupport (f : ComplexVector n × ComplexVector n × ℝ → ℝ)
    (a : ComplexVector n × ComplexVector n × ℝ)
    (p : (ComplexVector n × ComplexVector n × ℝ) →L[ℝ] ℝ)
    (A : (ComplexVector n × ComplexVector n × ℝ) →L[ℝ]
      (ComplexVector n × ComplexVector n × ℝ) →L[ℝ] ℝ)
    (α : ℝ) (y : ComplexVector n × ComplexVector n × ℝ) : ℝ :=
  jetPolynomial (f a) a p A y - α * coordinateSquare a y

theorem quadraticSupport_contDiff (f : ComplexVector n × ComplexVector n × ℝ → ℝ)
    (a : ComplexVector n × ComplexVector n × ℝ)
    (p : (ComplexVector n × ComplexVector n × ℝ) →L[ℝ] ℝ)
    (A : (ComplexVector n × ComplexVector n × ℝ) →L[ℝ]
      (ComplexVector n × ComplexVector n × ℝ) →L[ℝ] ℝ) (α : ℝ) :
    ContDiff ℝ ∞ (quadraticSupport f a p A α) :=
  (jetPolynomial_contDiff _ _ _ _).sub (contDiff_const.mul (coordinateSquare_contDiff a))

@[simp] theorem quadraticSupport_self (f : ComplexVector n × ComplexVector n × ℝ → ℝ)
    (a : ComplexVector n × ComplexVector n × ℝ)
    (p : (ComplexVector n × ComplexVector n × ℝ) →L[ℝ] ℝ)
    (A : (ComplexVector n × ComplexVector n × ℝ) →L[ℝ]
      (ComplexVector n × ComplexVector n × ℝ) →L[ℝ] ℝ) (α : ℝ) :
    quadraticSupport f a p A α a = f a := by
  simp [quadraticSupport, jetPolynomial]

/-- The only regularity input is the actual second Peano jet. The finite C²
germ supplies this through the separately published E02 bridge. -/
theorem quadraticSupport_strict_margin
    {f : ComplexVector n × ComplexVector n × ℝ → ℝ}
    {a : ComplexVector n × ComplexVector n × ℝ}
    {p : (ComplexVector n × ComplexVector n × ℝ) →L[ℝ] ℝ}
    {A : (ComplexVector n × ComplexVector n × ℝ) →L[ℝ]
      (ComplexVector n × ComplexVector n × ℝ) →L[ℝ] ℝ}
    (hf : RealSecondJet f a p A) {α : ℝ} (hα : 0 < α) :
    ∀ᶠ y in 𝓝 a, quadraticSupport f a p A α y +
      (α / 2) * coordinateSquare a y ≤ f y := by
  filter_upwards [hf.2.def (half_pos hα)] with y hy
  have hn := norm_sub_sq_le_coordinateSquare a y
  have hrem : -(α / 2) * coordinateSquare a y ≤
      f y - jetPolynomial (f a) a p A y := by
    have hlow := (abs_le.mp (by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖y - a‖)] using hy)).1
    dsimp [jetPolynomial]
    nlinarith [mul_le_mul_of_nonneg_left hn (half_pos hα).le]
  dsimp [quadraticSupport]
  linarith

end Yau.Blueprint.V01Proof

import Yau.Proofs.Y06TriangularBounds
import Yau.Proofs.Y06AllowedProjection
import Yau.Proofs.Y01SequenceEnvelopes

/-! Multiplicative coefficient sizes avoid losses depending on a finite horizon. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux

variable {n d : ℕ}

def polySize (P : PolyMap n) : ℝ := 1 + P.coeffNorm

theorem polySize_one_le (P : PolyMap n) : 1 ≤ polySize P := by
  dsimp [polySize]
  linarith [coeffNorm_nonneg P]

theorem polySize_add (P Q : PolyMap n) : polySize (P + Q) ≤ polySize P * polySize Q := by
  have h := coeffNorm_add_le P Q
  dsimp [polySize]
  nlinarith [coeffNorm_nonneg P, coeffNorm_nonneg Q]

theorem polySize_sub (P Q : PolyMap n) : polySize (P - Q) ≤ polySize P * polySize Q := by
  have h := coeffNorm_sub_le P Q
  dsimp [polySize]
  nlinarith [coeffNorm_nonneg P, coeffNorm_nonneg Q]

theorem polySize_comp (P Q : PolyMap n) (hP : P.degree ≤ d) :
    polySize (P.comp Q) ≤ polySize P * polySize Q ^ d := by
  have hcomp := (comp_coeffNorm_le P Q).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (polySize_one_le Q) hP) (coeffNorm_nonneg P))
  have hpow := one_le_pow₀ (polySize_one_le Q) (n := d)
  dsimp only [polySize] at *
  nlinarith

theorem polySize_homogeneousPart (m : ℕ) (P : PolyMap n) :
    polySize (homogeneousPart m P) ≤ polySize P := by
  exact add_le_add (le_refl 1) (coeffNorm_homogeneousPart_le m P)

theorem polySize_forbiddenProjection (w : Fin n → ℝ) (P : PolyMap n) :
    polySize (forbiddenProjection w P) ≤ polySize P :=
  add_le_add (le_refl 1) (forbiddenProjection_coeffNorm w P)

theorem polySize_allowedProjection (w : Fin n → ℝ) (P : PolyMap n) :
    polySize (allowedProjection w P) ≤ polySize P :=
  add_le_add (le_refl 1) (allowedProjection_coeffNorm w P)

theorem polySize_exp_add {P Q : PolyMap n} {A B x : ℝ}
    (hP : polySize P ≤ Real.exp (A * x)) (hQ : polySize Q ≤ Real.exp (B * x)) :
    polySize (P + Q) ≤ Real.exp ((A + B) * x) := by
  apply (polySize_add P Q).trans
  calc
    _ ≤ Real.exp (A * x) * Real.exp (B * x) :=
      mul_le_mul hP hQ (le_trans zero_le_one (polySize_one_le Q)) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem polySize_exp_sub {P Q : PolyMap n} {A B x : ℝ}
    (hP : polySize P ≤ Real.exp (A * x)) (hQ : polySize Q ≤ Real.exp (B * x)) :
    polySize (P - Q) ≤ Real.exp ((A + B) * x) := by
  apply (polySize_sub P Q).trans
  calc
    _ ≤ Real.exp (A * x) * Real.exp (B * x) :=
      mul_le_mul hP hQ (le_trans zero_le_one (polySize_one_le Q)) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem polySize_exp_comp {P Q : PolyMap n} {A B x : ℝ} (hdegree : P.degree ≤ d)
    (hP : polySize P ≤ Real.exp (A * x)) (hQ : polySize Q ≤ Real.exp (B * x)) :
    polySize (P.comp Q) ≤ Real.exp ((A + (d : ℝ) * B) * x) := by
  apply (polySize_comp P Q hdegree).trans
  calc
    _ ≤ Real.exp (A * x) * Real.exp (B * x) ^ d :=
      mul_le_mul hP (pow_le_pow_left₀ (le_trans zero_le_one (polySize_one_le Q)) hQ d)
        (pow_nonneg (le_trans zero_le_one (polySize_one_le Q)) d) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

theorem one_add_exp_enlarge {x A : ℝ} (hx : 1 ≤ x) :
    1 + Real.exp (A * x) ≤ Real.exp ((max 0 A + 1) * x) := by
  have hA : Real.exp (A * x) ≤ Real.exp (max 0 A * x) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith))
  have hge : 1 ≤ Real.exp (max 0 A * x) := Real.one_le_exp_iff.mpr (by positivity)
  have h2 : (2 : ℝ) ≤ Real.exp x := by
    have := Real.add_one_le_exp x
    linarith
  calc
    _ ≤ 2 * Real.exp (max 0 A * x) := by linarith
    _ ≤ Real.exp x * Real.exp (max 0 A * x) :=
      mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Yau.Proofs.Y06Aux

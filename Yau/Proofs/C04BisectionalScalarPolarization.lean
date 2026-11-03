import Yau.Proofs.C04BisectionalScalarMatrix

noncomputable section
open scoped Matrix ComplexOrder MatrixOrder
namespace Yau.Proofs.C04BisectionalScalarAux
open Yau Yau.Blueprint Yau.NodeProofs Yau.LeafProofs
variable {n : ℕ}

def curvatureValue (C : Fin n → Fin n → Fin n → Fin n → ℂ)
    (u v w z : Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l, C i j k l * u i * star (v j) * w k * star (z l)

theorem curvatureValue_polarize_first (C : Fin n → Fin n → Fin n → Fin n → ℂ)
    (u v w z : Fin n → ℂ) :
    4 * curvatureValue C u v w z =
      curvatureValue C (u+v) (u+v) w z - curvatureValue C (u-v) (u-v) w z +
        Complex.I * (curvatureValue C (u+Complex.I • v) (u+Complex.I • v) w z -
          curvatureValue C (u-Complex.I • v) (u-Complex.I • v) w z) := by
  simp only [curvatureValue, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, star_add, star_sub, star_mul, Complex.star_def,
    Complex.conj_I, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem curvatureValue_polarize_last (C : Fin n → Fin n → Fin n → Fin n → ℂ)
    (u v w z : Fin n → ℂ) :
    4 * curvatureValue C u v w z =
      curvatureValue C u v (w+z) (w+z) - curvatureValue C u v (w-z) (w-z) +
        Complex.I * (curvatureValue C u v (w+Complex.I • z) (w+Complex.I • z) -
          curvatureValue C u v (w-Complex.I • z) (w-Complex.I • z)) := by
  simp only [curvatureValue, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, star_add, star_sub, star_mul, Complex.star_def,
    Complex.conj_I, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem curvatureValue_star (C : Fin n → Fin n → Fin n → Fin n → ℂ)
    (hs : ∀ i j k l, star (C i j k l) = C j i l k)
    (u v w z : Fin n → ℂ) :
    star (curvatureValue C u v w z) = curvatureValue C v u z w := by
  simp only [curvatureValue, star_sum, star_mul, star_star, hs]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem curvatureValue_diagonal_real (C : Fin n → Fin n → Fin n → Fin n → ℂ)
    (hs : ∀ i j k l, star (C i j k l) = C j i l k)
    (u v : Fin n → ℂ) :
    curvatureValue C u u v v = ((curvatureValue C u u v v).re : ℂ) := by
  have hh := congrArg Complex.im (curvatureValue_star C hs u u v v)
  have hi : (curvatureValue C u u v v).im = 0 := by
    simp only [Complex.star_def, Complex.conj_im] at hh
    linarith
  apply Complex.ext <;> simp [hi]

theorem norm_le_of_polarization {t a b c d : ℂ} {B : ℝ}
    (hp : 4*t = a-b+Complex.I*(c-d))
    (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ B) (hd : ‖d‖ ≤ B) :
    ‖t‖ ≤ B := by
  have hh : (4 : ℝ)*‖t‖ ≤ (‖a‖+‖b‖)+(‖c‖+‖d‖) := by
    calc
      (4 : ℝ)*‖t‖ = ‖(4 : ℂ)*t‖ := by simp [norm_mul]
      _ = ‖a-b+Complex.I*(c-d)‖ := congrArg norm hp
      _ ≤ ‖a-b‖+‖Complex.I*(c-d)‖ := norm_add_le _ _
      _ ≤ (‖a‖+‖b‖)+(‖c‖+‖d‖) := by
        simpa [norm_mul] using add_le_add (norm_sub_le a b) (norm_sub_le c d)
  linarith

end Yau.Proofs.C04BisectionalScalarAux

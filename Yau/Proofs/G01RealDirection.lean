import Yau.Proofs.G01RawPairing

noncomputable section
open scoped Matrix
namespace Yau.NodeProofs.G01Aux
open Yau
variable {n : ℕ}

def realDirectionFactor (a : RIdx n) : ℂ := if a.2 = 0 then 1 else Complex.I

/-- Summing actual real coordinate directions reconstructs the mixed complex contraction. -/
theorem mixed_real_direction_contraction (B : Fin n → Fin n → ℂ)
    (U V : ComplexVector n) :
    (∑ a : RIdx n, ∑ b : RIdx n,
      (realDirectionFactor a * star (realDirectionFactor b) * B a.1 b.1 -
        realDirectionFactor b * star (realDirectionFactor a) * B b.1 a.1).re *
        realCoord U a * realCoord V b) =
      (∑ k, ∑ l, B k l * (U k * star (V l) - V k * star (U l))).re := by
  have hswap : (∑ a : RIdx n, ∑ b : RIdx n,
      (realDirectionFactor b * star (realDirectionFactor a) * B b.1 a.1).re *
        realCoord U a * realCoord V b) =
      ∑ a : RIdx n, ∑ b : RIdx n,
        (realDirectionFactor a * star (realDirectionFactor b) * B a.1 b.1).re *
          realCoord V a * realCoord U b := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp only [Complex.sub_re, sub_mul, Finset.sum_sub_distrib]
  rw [hswap, ← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, realDirectionFactor, realCoord]
  norm_num only [Fin.zero_eta, Fin.mk.injEq, ↓reduceIte]
  simp only [Complex.re_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  simp [Complex.mul_re, Complex.mul_im]
  ring

end Yau.NodeProofs.G01Aux

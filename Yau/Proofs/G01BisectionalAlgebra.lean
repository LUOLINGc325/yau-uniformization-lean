import Yau.Blueprint.NormalizationTargets

noncomputable section
open scoped Matrix
namespace Yau.NodeProofs.G01Aux
open Yau
variable {n : ℕ}

def mixedChernContraction (C : Fin n → Fin n → Fin n → Fin n → ℂ)
    (U V W Z : ComplexVector n) : ℂ :=
  ∑ k, ∑ l, (∑ j, ∑ i, C i j k l * W i * star (Z j)) *
    (U k * star (V l) - V k * star (U l))

/-- The second real section in the paper cancels the unwanted pure product. -/
theorem mixed_bisectional_sum (C : Fin n → Fin n → Fin n → Fin n → ℂ)
    (U V : ComplexVector n) :
    2 * (mixedChernContraction C U V V U).re +
      2 * (mixedChernContraction C U (Complex.I • V) (Complex.I • V) U).re =
      4 * (∑ k, ∑ l, ∑ j, ∑ i,
        C i j k l * V i * star (U j) * U k * star (V l)).re := by
  simp only [mixedChernContraction, PiLp.smul_apply, smul_eq_mul, star_mul,
    Finset.sum_mul, Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- Holomorphic Kähler symmetry aligns the section contraction with the Chern bisectional form. -/
theorem holomorphic_symmetry_contraction (C : Fin n → Fin n → Fin n → Fin n → ℂ)
    (hC : ∀ i j k l, C i j k l = C k j i l) (U V : ComplexVector n) :
    (∑ k, ∑ l, ∑ j, ∑ i, C i j k l * V i * star (U j) * U k * star (V l)) =
      ∑ i, ∑ j, ∑ k, ∑ l, C i j k l * U i * star (U j) * V k * star (V l) := by
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  rw [hC i j k l]
  ring

end Yau.NodeProofs.G01Aux

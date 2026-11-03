import Yau.LeafProofs.L14MatrixIMS
import Yau.LeafProofs.L14PositiveAlgebra

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped ComplexOrder Matrix Kronecker
open Yau

namespace Yau.LeafProofs.L14Aux

theorem finite_twoCoefficient_IMS {n r : ℕ} {ι : Type*} [Fintype ι]
    (G : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin r) (Fin r) ℂ)
    (hG : G.PosDef) (hH : H.PosDef) (χ : ι → ℝ)
    (T : Fin r → Fin n → Fin n → ℂ) (A : ι → Fin r → Fin n → Fin n → ℂ)
    (hχ : ∑ i, χ i ^ 2 = 1) (hA : ∀ α i j, ∑ k, (χ k : ℂ) * A k α i j = 0) :
    (∑ k, twoCoefficientNormSq G H (fun α i j => (χ k : ℂ) * T α i j + A k α i j)) =
      twoCoefficientNormSq G H T + ∑ k, twoCoefficientNormSq G H (A k) := by
  have he := finite_matrix_IMS ((H ⊗ₖ G⁻¹) ⊗ₖ G⁻¹)
    ((hH.kronecker hG.inv).kronecker hG.inv) χ
    (fun p : (Fin r × Fin n) × Fin n => T p.1.1 p.1.2 p.2)
    (fun k p => A k p.1.1 p.1.2 p.2) hχ (by
      funext p
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hA p.1.1 p.1.2 p.2)
  have hnorm (T : Fin r → Fin n → Fin n → ℂ) : twoCoefficientNormSq G H T =
      (1 / 2 : ℝ) * (star (fun p : (Fin r × Fin n) × Fin n => T p.1.1 p.1.2 p.2) ⬝ᵥ
        ((H ⊗ₖ G⁻¹) ⊗ₖ G⁻¹) *ᵥ (fun p => T p.1.1 p.1.2 p.2)).re := by
    unfold twoCoefficientNormSq
    rw [twoCoefficient_contraction_eq_kronecker]
    norm_num [Complex.mul_re]
  simp_rw [hnorm]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_add]
  apply congrArg ((1 / 2 : ℝ) * ·)
  convert he using 1

theorem finite_positiveTensor_IMS {n r : ℕ} {ι : Type*} [Fintype ι]
    (G : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin r) (Fin r) ℂ)
    (hG : G.PosDef) (hH : H.PosDef) (χ : ι → ℝ)
    (D : Fin r → Matrix (Fin n) (Fin n) ℂ) (A : ι → Fin r → Matrix (Fin n) (Fin n) ℂ)
    (hχ : ∑ i, χ i ^ 2 = 1) (hA : ∀ α i j, ∑ k, (χ k : ℂ) * A k α i j = 0) :
    (∑ k, (positiveTensorContraction G H (fun α i j => (χ k : ℂ) * D α i j + A k α i j)).re) =
      (positiveTensorContraction G H D).re + ∑ k, (positiveTensorContraction G H (A k)).re := by
  have he := finite_matrix_IMS ((H ⊗ₖ G⁻¹) ⊗ₖ G)
    ((hH.kronecker hG.inv).kronecker hG) χ
    (fun p : (Fin r × Fin n) × Fin n => D p.1.1 p.1.2 p.2)
    (fun k p => A k p.1.1 p.1.2 p.2) hχ (by
      funext p
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hA p.1.1 p.1.2 p.2)
  have hnorm (D : Fin r → Matrix (Fin n) (Fin n) ℂ) : positiveTensorContraction G H D =
      star (fun p : (Fin r × Fin n) × Fin n => D p.1.1 p.1.2 p.2) ⬝ᵥ
        ((H ⊗ₖ G⁻¹) ⊗ₖ G) *ᵥ (fun p => D p.1.1 p.1.2 p.2) :=
    weighted_trace_remainder_eq_kronecker G H D
  simp_rw [hnorm]
  convert he using 1

theorem rankOne_positive_energy_eq_wedge_add_contraction {n r : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin r) (Fin r) ℂ)
    (hG : G.PosDef) (a : Fin n → ℂ) (W : Fin r → Fin n → ℂ) :
    (positiveTensorContraction G H (fun α => Matrix.vecMulVec a (W α))).re =
      twoCoefficientNormSq G H (fun α i j => a i * (G *ᵥ W α) j - a j * (G *ᵥ W α) i) +
      (star (fun α => star a ⬝ᵥ W α) ⬝ᵥ H *ᵥ (fun α => star a ⬝ᵥ W α)).re := by
  have hp : positiveTensorContraction G H (fun α => Matrix.vecMulVec a (W α)) =
      (star a ⬝ᵥ G⁻¹ *ᵥ a) * ∑ α, ∑ β, H α β * (star (W α) ⬝ᵥ G *ᵥ W β) := by
    simp only [positiveTensorContraction, rankOne_positive_trace, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    ring
  rw [hp, Complex.mul_re,
    show (star a ⬝ᵥ G⁻¹ *ᵥ a).im = 0 from
      (Complex.nonneg_iff.mp (hG.inv.posSemidef.dotProduct_mulVec_nonneg a)).2.symm,
    zero_mul, sub_zero]
  exact (wedge_contraction_energy_identity G H hG a W).symm

theorem finite_BKN_IMS {n r : ℕ} {ι : Type*} [Fintype ι]
    (G : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin r) (Fin r) ℂ)
    (hG : G.PosDef) (hH : H.PosDef) (χ : ι → ℝ)
    (a : ι → Fin n → ℂ) (W : Fin r → Fin n → ℂ)
    (T : Fin r → Fin n → Fin n → ℂ) (S : Fin r → ℂ)
    (D : Fin r → Matrix (Fin n) (Fin n) ℂ)
    (hχ : ∑ i, χ i ^ 2 = 1) (ha : ∀ i, ∑ k, (χ k : ℂ) * a k i = 0) :
    (∑ k : ι, (twoCoefficientNormSq G H
      (fun α i j => (χ k : ℂ) * T α i j + (a k i * (G *ᵥ W α) j - a k j * (G *ᵥ W α) i)) +
      (star (fun α => (χ k : ℂ) * S α - star (a k) ⬝ᵥ W α) ⬝ᵥ H *ᵥ
        (fun α => (χ k : ℂ) * S α - star (a k) ⬝ᵥ W α)).re -
      (positiveTensorContraction G H (fun (α : Fin r) (i j : Fin n) => (χ k : ℂ) * D α i j + a (k : ι) i * W α j)).re)) =
    twoCoefficientNormSq G H T + (star S ⬝ᵥ H *ᵥ S).re - (positiveTensorContraction G H D).re := by
  let B := fun k α i j => a k i * (G *ᵥ W α) j - a k j * (G *ᵥ W α) i
  let C := fun k α => -(star (a k) ⬝ᵥ W α)
  let P := fun k α => Matrix.vecMulVec (a k) (W α)
  have hB (α : Fin r) (i j : Fin n) : ∑ k, (χ k : ℂ) * B k α i j = 0 := by
    simp only [B, mul_sub, Finset.sum_sub_distrib, ← mul_assoc, ← Finset.sum_mul, ha,
      zero_mul, sub_self]
  have hstar (i : Fin n) : ∑ k, (χ k : ℂ) * star (a k i) = 0 := by
    have he := congrArg star (ha i)
    simpa only [star_sum, star_mul, Complex.star_def, Complex.conj_ofReal, star_zero, mul_comm] using he
  have hC : ∑ k, (χ k : ℂ) • C k = 0 := by
    funext α
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, C, mul_neg,
      Finset.sum_neg_distrib, dotProduct, Pi.star_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [← mul_assoc, ← Finset.sum_mul, hstar, zero_mul, Finset.sum_const_zero,
      neg_zero, Pi.zero_apply]
  have hP (α : Fin r) (i j : Fin n) : ∑ k, (χ k : ℂ) * P k α i j = 0 := by
    simp only [P, Matrix.vecMulVec_apply, ← mul_assoc, ← Finset.sum_mul, ha, zero_mul]
  have heB := finite_twoCoefficient_IMS G H hG hH χ T B hχ hB
  have heC := finite_matrix_IMS H hH χ S C hχ hC
  have heP := finite_positiveTensor_IMS G H hG hH χ D P hχ hP
  have hneg (v : Fin r → ℂ) : (star (-v) ⬝ᵥ H *ᵥ (-v)).re = (star v ⬝ᵥ H *ᵥ v).re := by
    rw [Matrix.mulVec_neg, star_neg, dotProduct_neg, neg_dotProduct, neg_neg]
  have herr (k : ι) : (positiveTensorContraction G H (P k)).re =
      twoCoefficientNormSq G H (B k) + (star (C k) ⬝ᵥ H *ᵥ C k).re := by
    rw [show C k = -(fun α => star (a k) ⬝ᵥ W α) from rfl, hneg]
    exact rankOne_positive_energy_eq_wedge_add_contraction G H hG (a k) W
  change (∑ k : ι, (twoCoefficientNormSq G H (fun α i j => (χ k : ℂ) * T α i j + B k α i j) +
    (star ((χ k : ℂ) • S + C k) ⬝ᵥ H *ᵥ ((χ k : ℂ) • S + C k)).re -
    (positiveTensorContraction G H (fun α i j => (χ k : ℂ) * D α i j + P k α i j)).re)) = _
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, heB, heC, heP]
  simp_rw [herr, Finset.sum_add_distrib]
  ring

end Yau.LeafProofs.L14Aux

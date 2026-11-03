import Yau.Proofs.F01FiniteProductLower
import Yau.Proofs.F01SimultaneousHermitian
import Yau.LeafProofs.L17ChartNaturality

/-! The actual determinant quotient and an actual upper Hermitian order
give a quantitative lower Hermitian order, in every dimension. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau.LeafProofs.L17Aux
variable {n : ℕ}

theorem metric_lower_of_determinant_and_upper
    {H K : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef) (hK : K.PosDef)
    {C d : ℝ} (hC : 1 ≤ C)
    (hupper : ((C : ℂ) • H - K).PosSemidef)
    (hdet : d ≤ K.det.re / H.det.re) :
    (K - ((d / C ^ n : ℝ) : ℂ) • H).PosSemidef := by
  obtain ⟨J, hJ, hnormal, values, hdiag⟩ :=
    simultaneous_hermitian_normalization H K hH hK.isHermitian
  have hJdet : J.det ≠ 0 := (hJ.map Matrix.detMonoidHom).ne_zero
  have hdiagpos : (Matrix.diagonal (fun i => (values i : ℂ))).PosDef := by
    rw [← hdiag]
    exact hK.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hJ)
  have hvpos (i : Fin n) : 0 < values i :=
    Complex.zero_lt_real.mp ((Matrix.posDef_diagonal_iff.mp hdiagpos) i)
  have hu := hupper.conjTranspose_mul_mul_same J
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    hnormal, hdiag] at hu
  have hvupper (i : Fin n) : values i ≤ C := by
    have hi := (Complex.nonneg_iff.mp (hu.diag_nonneg (i := i))).1
    simpa only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one, Matrix.diagonal_apply_eq, Complex.sub_re, Complex.ofReal_re,
      sub_nonneg] using hi
  have hratio := determinant_ratio_congruence K H J hJdet
  rw [hdiag, hnormal, Matrix.det_one, Complex.one_re, div_one, Matrix.det_diagonal] at hratio
  have hprodComplex : (∏ i, (values i : ℂ)) = ((∏ i, values i : ℝ) : ℂ) := by
    norm_cast
  rw [hprodComplex, Complex.ofReal_re] at hratio
  have hvlo (i : Fin n) : d / C ^ n ≤ values i := by
    simpa only [Fintype.card_fin] using finite_factor_lower_of_product values hC
      (fun j => (hvpos j).le) hvupper (by rw [hratio]; exact hdet) i
  have hnonneg (i : Fin n) : (0 : ℂ) ≤ ((values i - d / C ^ n : ℝ) : ℂ) :=
    Complex.zero_le_real.mpr (sub_nonneg.mpr (hvlo i))
  have hdiaglower : (Matrix.diagonal (fun i => (values i : ℂ)) -
      ((d / C ^ n : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
    have hp := Matrix.PosSemidef.diagonal hnonneg
    convert hp using 1
    ext i j
    by_cases hij : i = j <;>
      simp [Matrix.diagonal_apply, Matrix.one_apply, hij, Complex.ofReal_sub]
  have hlower : (Jᴴ * (K - ((d / C ^ n : ℝ) : ℂ) • H) * J).PosSemidef := by
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      hnormal, hdiag] using hdiaglower
  exact (Matrix.IsUnit.posSemidef_star_left_conjugate_iff hJ).mp hlower

end Yau.NodeProofs.F01Aux

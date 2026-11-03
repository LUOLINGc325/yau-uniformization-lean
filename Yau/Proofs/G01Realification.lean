import Yau.Blueprint.NormalizationTargets
import Yau.LeafProofs.L12

noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.G01Aux
open Yau Yau.LeafProofs
variable {n : ℕ}

/-- Raw realification, before the symmetric projection used by `Parabolic.iota`. -/
def rawReal (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (RIdx n) (RIdx n) ℝ :=
  fun a b => if a.2 = b.2 then (A a.1 b.1).re
    else if a.2 = 0 then -(A a.1 b.1).im else (A a.1 b.1).im

theorem rawReal_mul (A B : Matrix (Fin n) (Fin n) ℂ) :
    rawReal (A * B) = rawReal A * rawReal B := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [rawReal, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im, Finset.sum_add_distrib, Finset.sum_sub_distrib] <;> ring

theorem rawReal_trace (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (rawReal A) = 2 * (Matrix.trace A).re := by
  simp [Matrix.trace, rawReal, Fintype.sum_prod_type,
    Complex.re_sum, ← Finset.sum_add_distrib, two_mul]

theorem rawReal_one : rawReal (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a <;> fin_cases b <;> by_cases hij : i = j <;>
    simp [rawReal, Matrix.one_apply, hij]

/-- Hermitian coefficients give a symmetric raw real matrix. -/
theorem rawReal_isSymm (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    (rawReal A).IsSymm := by
  ext ⟨i, a⟩ ⟨j, b⟩
  have hre := congrArg Complex.re (hA.apply i j)
  have him := congrArg Complex.im (hA.apply i j)
  fin_cases a <;> fin_cases b <;>
    simp only [Complex.star_def, Complex.conj_re, Complex.conj_im] at hre him <;>
    simp [rawReal, Matrix.transpose_apply, hre, him]
  linarith

/-- The projected `iota` agrees with raw realification precisely here under Hermiticity. -/
theorem rawReal_eq_iota (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    rawReal A = (Parabolic.iota A : Parabolic.Mat n) := by
  change rawReal A = (selfAdjointPart ℝ (rawReal A) : Parabolic.Mat n)
  exact ((show IsSelfAdjoint (rawReal A) from rawReal_isSymm A hA).coe_selfAdjointPart_apply ℝ).symm

theorem hermitianRealification_eq (A : Matrix (Fin n) (Fin n) ℂ) :
    L12Aux.hermitianRealification A = (2 : ℝ) • rawReal A := by
  rfl

variable {M : ComplexManifold n}

theorem realMetricFn_eq_rawReal (h : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) :
    realMetricFn h x z = (2 : ℝ) • rawReal (hMat h x z) := by
  ext a b
  exact L12Aux.realMetricFn_entries h x z a b

/-- The genuine real metric inverse, without a determinant-realification shortcut. -/
theorem realMetricFn_inverse_eq (h : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) :
    (realMetricFn h x z)⁻¹ = (1 / 2 : ℝ) • rawReal (hMat h x z)⁻¹ := by
  have hH := (L12Aux.hMat_posDef h x z hz).isUnit.map Matrix.detMonoidHom
  have hG := isUnit_iff_ne_zero.mpr (L12Aux.realMetricFn_posDef h x z hz).det_pos.ne'
  have hmul : realMetricFn h x z * ((1 / 2 : ℝ) • rawReal (hMat h x z)⁻¹) = 1 := by
    rw [realMetricFn_eq_rawReal, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul, ← rawReal_mul,
      Matrix.mul_nonsing_inv _ hH, rawReal_one]
  calc
    (realMetricFn h x z)⁻¹ =
        (realMetricFn h x z)⁻¹ *
          (realMetricFn h x z * ((1 / 2 : ℝ) • rawReal (hMat h x z)⁻¹)) := by rw [hmul, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hG, Matrix.one_mul]

end Yau.NodeProofs.G01Aux

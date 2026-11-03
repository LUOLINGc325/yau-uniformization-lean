import Yau.Proofs.V04WallErrorTraceDet

/-! The inverse trace is controlled by the actual determinant ratio when
the evolving metric lies below the initial metric. -/

open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hermitian_det_eq_ofReal_re {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    A.det = (A.det.re : ℂ) := by
  change A.det = ((RCLike.re A.det : ℝ) : ℂ)
  rw [hA.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod, RCLike.ofReal_re]
  rfl

theorem relative_inverse_trace_le_det_ratio
    {H G : Matrix ι ι ℂ} (hH : H.PosDef) (hG : G.PosDef) (hle : (G - H).PosSemidef) :
    (Matrix.trace (H⁻¹ * G)).re ≤
      (Fintype.card ι : ℝ) * (G.det.re / H.det.re) := by
  let R := CFC.sqrt H
  let S := R⁻¹
  have hRR : R * R = H := CFC.sqrt_mul_sqrt_self H hH.posSemidef.nonneg
  have hR : IsUnit R := isUnit_of_mul_isUnit_left (hRR.symm ▸ hH.isUnit)
  have hRdet : IsUnit R.det := hR.map Matrix.detMonoidHom
  have hS : S.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg H)).isHermitian.inv
  have hSHS : S * H * S = 1 := by
    calc
      S * H * S = (S * R) * (R * S) := by rw [← hRR]; noncomm_ring
      _ = 1 := by
        rw [show S * R = 1 from Matrix.nonsing_inv_mul R hRdet,
          show R * S = 1 from Matrix.mul_nonsing_inv R hRdet, Matrix.one_mul]
  have hSS : S * S = H⁻¹ := by
    change R⁻¹ * R⁻¹ = H⁻¹
    rw [← Matrix.mul_inv_rev, hRR]
  let K := S * G * S
  have hK : K.PosSemidef := by
    simpa only [hS.eq] using hG.posSemidef.conjTranspose_mul_mul_same S
  have hKlo : (K - 1).PosSemidef := by
    have hp := hle.conjTranspose_mul_mul_same S
    simpa only [hS.eq, Matrix.mul_sub, Matrix.sub_mul, hSHS] using hp
  have htrace : Matrix.trace K = Matrix.trace (H⁻¹ * G) := by
    change Matrix.trace (S * G * S) = _
    rw [Matrix.trace_mul_cycle, hSS]
  have hdet : K.det = G.det * H.det⁻¹ := by
    calc
      K.det = G.det * (S * S).det := by simp only [K, Matrix.det_mul]; ring
      _ = G.det * H.det⁻¹ := by rw [hSS, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  have hdetR : K.det.re = G.det.re / H.det.re := by
    rw [hdet, hermitian_det_eq_ofReal_re hH.isHermitian,
      hermitian_det_eq_ofReal_re hG.isHermitian, ← Complex.ofReal_inv,
      ← Complex.ofReal_mul, Complex.ofReal_re, div_eq_mul_inv]
    simp
  have hp := trace_le_card_mul_det_of_sub_one_posSemidef hK.isHermitian hKlo
  rwa [htrace, hdetR] at hp

end Yau.Blueprint.V04Proof.WallErrorAux

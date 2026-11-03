import Yau.Proofs.V04DiscMatrixMaximum

/-! Unit test directions are obtained only where the actual matrix upper
bound fails. Thus empty index types do not require a fixed unit vector. -/

open scoped Matrix ComplexOrder Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n : ℕ}

theorem quadValue_smul (A : CotangentMatrix n) (c : ℂ) (v : CotangentIndex n → ℂ) :
    quadValue A (c • v) = ‖c‖ ^ 2 * quadValue A v := by
  unfold quadValue
  rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  rw [← mul_assoc, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem quadValue_sub (A B : CotangentMatrix n) (v : CotangentIndex n → ℂ) :
    quadValue (A - B) v = quadValue A v - quadValue B v := by
  simp only [quadValue, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]

theorem quadValue_real_smul (A : CotangentMatrix n) (c : ℝ) (v : CotangentIndex n → ℂ) :
    quadValue ((c : ℂ) • A) v = c * quadValue A v := by
  simp only [quadValue, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem quadValue_congruence (A B : CotangentMatrix n) (v : CotangentIndex n → ℂ) :
    quadValue (Bᴴ * A * B) v = quadValue A (B *ᵥ v) := by
  simp only [quadValue, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]

theorem quadValue_one (v : EuclideanSpace ℂ (CotangentIndex n)) :
    quadValue (1 : CotangentMatrix n) (WithLp.ofLp v) = ‖v‖ ^ 2 := by
  rw [quadValue, Matrix.one_mulVec]
  change (∑ i, star (v i) * v i).re = ‖v‖ ^ 2
  rw [Complex.re_sum, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    Complex.ofReal_re]

theorem posSemidef_iff_quadValue_unit (A : CotangentMatrix n) (hA : A.IsHermitian) :
    A.PosSemidef ↔ ∀ v : EuclideanSpace ℂ (CotangentIndex n),
      ‖v‖ = 1 → 0 ≤ quadValue A (WithLp.ofLp v) := by
  constructor
  · intro h v _
    exact h.re_dotProduct_nonneg _
  · intro h
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hA
    intro v
    apply Complex.nonneg_iff.mpr
    refine ⟨?_, (hA.im_star_dotProduct_mulVec_self v).symm⟩
    by_cases hv : v = 0
    · simp [hv]
    · let V : EuclideanSpace ℂ (CotangentIndex n) := WithLp.toLp 2 v
      have hV : V ≠ 0 := by
        intro hz
        apply hv
        exact congrArg WithLp.ofLp hz
      have hn : 0 < ‖V‖ := norm_pos_iff.mpr hV
      let c : ℂ := ((‖V‖⁻¹ : ℝ) : ℂ)
      let w : EuclideanSpace ℂ (CotangentIndex n) := c • V
      have hw : ‖w‖ = 1 := by
        simp [w, c, norm_smul, hn.ne']
      have htest := h w hw
      have hsmul : WithLp.ofLp w = c • v := rfl
      rw [hsmul, quadValue_smul] at htest
      have hc : 0 < ‖c‖ ^ 2 := by
        dsimp [c]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
        exact sq_pos_of_pos (inv_pos.mpr hn)
      exact nonneg_of_mul_nonneg_right htest hc

theorem exists_unit_quadValue_neg (A : CotangentMatrix n) (hA : A.IsHermitian)
    (hnot : ¬ A.PosSemidef) :
    ∃ v : EuclideanSpace ℂ (CotangentIndex n), ‖v‖ = 1 ∧ quadValue A (WithLp.ofLp v) < 0 := by
  rw [posSemidef_iff_quadValue_unit A hA] at hnot
  push Not at hnot
  exact hnot

theorem center_majorant_unit_violation (Φ H Hinv : CotangentMatrix n) (hΦ : Φ.IsHermitian)
    (hHI : H * Hinv = 1) (hIH : Hinv * H = 1) (c r : ℝ)
    (hnot : ¬ (((1 + r : ℝ) : ℂ) • (Hᴴ * H) - (c : ℂ) • Φ).PosSemidef) :
    ∃ v : EuclideanSpace ℂ (CotangentIndex n), ‖v‖ = 1 ∧
      1 + r < c * quadValue Φ (Hinv *ᵥ WithLp.ofLp v) := by
  let A := (((1 + r : ℝ) : ℂ) • (Hᴴ * H) - (c : ℂ) • Φ)
  let S := Hinvᴴ * A * Hinv
  have hreal (t : ℝ) : IsSelfAdjoint (t : ℂ) := by
    change star (t : ℂ) = (t : ℂ)
    simp
  have hA : A.IsHermitian :=
    ((Matrix.isHermitian_conjTranspose_mul_self H).smul (hreal (1 + r))).sub (hΦ.smul (hreal c))
  have hS : S.IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul Hinv hA
  have hnotS : ¬ S.PosSemidef := by
    intro hpos
    have hback := hpos.conjTranspose_mul_mul_same H
    have hbackeq : Hᴴ * S * H = A := by
      calc
        _ = (Hinv * H)ᴴ * A * (Hinv * H) := by
          dsimp [S]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = A := by rw [hIH]; simp
    rw [hbackeq] at hback
    exact hnot hback
  obtain ⟨v, hv, hneg⟩ := exists_unit_quadValue_neg S hS hnotS
  have hgram : Hinvᴴ * (Hᴴ * H) * Hinv = 1 := by
    calc
      _ = (H * Hinv)ᴴ * (H * Hinv) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hHI]; simp
  have hSform : S = (((1 + r : ℝ) : ℂ) • (1 : CotangentMatrix n) -
      (c : ℂ) • (Hinvᴴ * Φ * Hinv)) := by
    dsimp [S, A]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.smul_mul, hgram]
  rw [hSform, quadValue_sub, quadValue_real_smul, quadValue_real_smul,
    quadValue_congruence, quadValue_one, hv] at hneg
  refine ⟨v, hv, ?_⟩
  norm_num only [one_pow, mul_one] at hneg
  linarith

end Yau.Blueprint.V04Proof

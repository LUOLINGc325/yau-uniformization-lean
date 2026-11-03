import Yau.Proofs.F04CovectorMatrix

/-! A genuine matrix Cauchy bound for the two mixed Levi rank-one terms. -/
noncomputable section
open scoped ComplexOrder Matrix
namespace Yau.Proofs.F03Aux
open Yau Blueprint

theorem covector_cross_bound_of_rankOne_bounds {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n → ℂ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : HermLE (Matrix.vecMulVec (star c) c) (Complex.ofReal (a^2) • G))
    (hd : HermLE (Matrix.vecMulVec (star d) d) (Complex.ofReal (b^2) • G)) :
    HermLE (Matrix.vecMulVec (star c) d+Matrix.vecMulVec (star d) c)
      (Complex.ofReal (2*a*b) • G) := by
  let v : Fin n → ℂ := (b:ℂ) • c-(a:ℂ) • d
  have hOuter := Matrix.posSemidef_vecMulVec_star_self v
  unfold HermLE at hc hd ⊢
  have hTotal := (hOuter.add (hc.smul (Complex.zero_le_real.mpr (sq_nonneg b)))).add
    (hd.smul (Complex.zero_le_real.mpr (sq_nonneg a)))
  have hPositive := hTotal.smul (Complex.zero_le_real.mpr
    (show 0 ≤ 1/(a*b) from by positivity))
  convert hPositive using 1
  ext i j
  simp only [v,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.vecMulVec_apply,Pi.sub_apply,Pi.smul_apply,Pi.star_apply,
    star_sub,star_mul,Complex.star_def,Complex.conj_ofReal,
    Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_one]
  have haC : (a:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hbC : (b:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  field_simp
  <;> norm_num
  <;> ring

theorem covector_rankOne_bound_of_dual_bound {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosDef) (c : Fin n → ℂ)
    {a : ℝ} (hc : dualNormMat G (WithLp.toLp 2 c) ≤ a^2) :
    HermLE (Matrix.vecMulVec (star c) c) (Complex.ofReal (a^2) • G) := by
  have hRank := F04Proof.covector_rankOne_bound G hG c
  have hError := hG.posSemidef.smul (Complex.zero_le_real.mpr (sub_nonneg.mpr hc))
  unfold HermLE at hRank ⊢
  convert hRank.add hError using 1
  ext i j
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Complex.ofReal_sub]
  ring

theorem covector_cross_bound {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosDef) (c d : Fin n → ℂ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : dualNormMat G (WithLp.toLp 2 c) ≤ a^2)
    (hd : dualNormMat G (WithLp.toLp 2 d) ≤ b^2) :
    HermLE (Matrix.vecMulVec (star c) d+Matrix.vecMulVec (star d) c)
      (Complex.ofReal (2*a*b) • G) :=
  covector_cross_bound_of_rankOne_bounds G c d ha hb
    (covector_rankOne_bound_of_dual_bound G hG c hc)
    (covector_rankOne_bound_of_dual_bound G hG d hd)

end Yau.Proofs.F03Aux

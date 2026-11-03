import Yau.Proofs.F04CovectorMatrix

open scoped Matrix ComplexOrder

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

def covectorCross {n : ℕ} (c d : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.vecMulVec (star c) d + Matrix.vecMulVec (star d) c

theorem covector_cross_bound {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosDef)
    (c d : Fin n → ℂ) :
    let q := dualNormMat G (WithLp.toLp 2 c) + dualNormMat G (WithLp.toLp 2 d)
    HermLE (((-q : ℝ) : ℂ) • G) (covectorCross c d) ∧
      HermLE (covectorCross c d) ((q : ℂ) • G) := by
  let qc := dualNormMat G (WithLp.toLp 2 c)
  let qd := dualNormMat G (WithLp.toLp 2 d)
  have hc : ((qc : ℂ) • G - Matrix.vecMulVec (star c) c).PosSemidef :=
    covector_rankOne_bound G hG c
  have hd : ((qd : ℂ) • G - Matrix.vecMulVec (star d) d).PosSemidef :=
    covector_rankOne_bound G hG d
  have hminus : (Matrix.vecMulVec (star c) c + Matrix.vecMulVec (star d) d - covectorCross c d).PosSemidef := by
    have heq : Matrix.vecMulVec (star c) c + Matrix.vecMulVec (star d) d - covectorCross c d =
        Matrix.vecMulVec (star (c - d)) (c - d) := by
      ext i j
      simp only [covectorCross, Matrix.add_apply, Matrix.sub_apply, Matrix.vecMulVec_apply,
        Pi.star_apply, Pi.sub_apply, star_sub]
      ring
    rw [heq]
    exact Matrix.posSemidef_vecMulVec_star_self (c - d)
  have hplus : (Matrix.vecMulVec (star c) c + Matrix.vecMulVec (star d) d + covectorCross c d).PosSemidef := by
    have heq : Matrix.vecMulVec (star c) c + Matrix.vecMulVec (star d) d + covectorCross c d =
        Matrix.vecMulVec (star (c + d)) (c + d) := by
      ext i j
      simp only [covectorCross, Matrix.add_apply, Matrix.vecMulVec_apply, Pi.star_apply,
        Pi.add_apply, star_add]
      ring
    rw [heq]
    exact Matrix.posSemidef_vecMulVec_star_self (c + d)
  constructor
  · have hh := (hc.add hd).add hplus
    have heq : covectorCross c d - (((-(qc + qd) : ℝ) : ℂ) • G) =
        ((qc : ℂ) • G - Matrix.vecMulVec (star c) c +
          ((qd : ℂ) • G - Matrix.vecMulVec (star d) d)) +
          (Matrix.vecMulVec (star c) c + Matrix.vecMulVec (star d) d + covectorCross c d) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Complex.ofReal_neg, Complex.ofReal_add]
      ring
    change (covectorCross c d - (((-(qc + qd) : ℝ) : ℂ) • G)).PosSemidef
    rw [heq]
    exact hh
  · have hh := (hc.add hd).add hminus
    have heq : ((qc + qd : ℝ) : ℂ) • G - covectorCross c d =
        ((qc : ℂ) • G - Matrix.vecMulVec (star c) c +
          ((qd : ℂ) • G - Matrix.vecMulVec (star d) d)) +
          (Matrix.vecMulVec (star c) c + Matrix.vecMulVec (star d) d - covectorCross c d) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_add]
      ring
    change ((((qc + qd : ℝ) : ℂ) • G) - covectorCross c d).PosSemidef
    rw [heq]
    exact hh

end Yau.F04Proof

import Yau.Proofs.F04WeightedCross

open scoped Matrix ComplexOrder

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

theorem positive_weight_covector_cross_bound {n : ℕ} (G : Herm n) (hG : G.PosDef)
    (c d : Fin n → ℂ) {a : ℝ} (ha : 0 < a) :
    let q := dualNormMat G (WithLp.toLp 2 c) / a + a * dualNormMat G (WithLp.toLp 2 d)
    HermLE (((-q : ℝ) : ℂ) • G) (covectorCross c d) ∧
      HermLE (covectorCross c d) ((q : ℂ) • G) := by
  have hs : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have hh := weighted_covector_cross_bound G hG c d (Real.sqrt a)⁻¹ (inv_ne_zero hs)
  dsimp only at hh ⊢
  rw [inv_pow, Real.sq_sqrt ha.le, inv_inv, Real.sq_sqrt ha.le] at hh
  simpa only [div_eq_mul_inv, mul_comm] using hh

end Yau.F04Proof

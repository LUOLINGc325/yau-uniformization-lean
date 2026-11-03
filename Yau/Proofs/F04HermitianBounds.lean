import Yau.Proofs.F04SymmetricBounds
import Yau.Proofs.F04CovectorMatrix

open scoped Matrix ComplexOrder

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

theorem symmetric_bound_enlarge {n : ℕ} {G A : Herm n} (hG : G.PosSemidef)
    {a b : ℝ} (hab : a ≤ b)
    (hl : HermLE (((-a : ℝ) : ℂ) • G) A) (hu : HermLE A ((a : ℂ) • G)) :
    HermLE (((-b : ℝ) : ℂ) • G) A ∧ HermLE A ((b : ℂ) • G) :=
  ⟨hermLE_trans (hermLE_scalar_mono G hG (neg_le_neg hab)) hl,
    hermLE_trans hu (hermLE_scalar_mono G hG hab)⟩

theorem symmetric_bound_add {n : ℕ} {G A B : Herm n} {a b : ℝ}
    (hAl : HermLE (((-a : ℝ) : ℂ) • G) A) (hAu : HermLE A ((a : ℂ) • G))
    (hBl : HermLE (((-b : ℝ) : ℂ) • G) B) (hBu : HermLE B ((b : ℂ) • G)) :
    HermLE (((-(a + b) : ℝ) : ℂ) • G) (A + B) ∧
      HermLE (A + B) (((a + b : ℝ) : ℂ) • G) := by
  have hL := hermLE_add hAl hBl
  have hU := hermLE_add hAu hBu
  constructor
  · convert hL using 1
    rw [← add_smul, ← Complex.ofReal_add, neg_add]
  · convert hU using 1
    rw [← add_smul, ← Complex.ofReal_add]

theorem symmetric_rankOne_bound {n : ℕ} (G : Herm n) (hG : G.PosDef)
    (c : Fin n → ℂ) {b : ℝ} (hb : 0 ≤ b)
    (hc : dualNormMat G (WithLp.toLp 2 c) ≤ b) :
    HermLE (((-b : ℝ) : ℂ) • G) (Matrix.vecMulVec (star c) c) ∧
      HermLE (Matrix.vecMulVec (star c) c) ((b : ℂ) • G) := by
  have h0 : HermLE (0 : Herm n) (Matrix.vecMulVec (star c) c) := by
    change (Matrix.vecMulVec (star c) c - 0).PosSemidef
    rw [sub_zero]
    exact Matrix.posSemidef_vecMulVec_star_self c
  constructor
  · have hz := hermLE_scalar_mono G hG.posSemidef (show -b ≤ 0 by linarith)
    simp only [Complex.ofReal_zero, zero_smul] at hz
    exact hermLE_trans hz h0
  · exact hermLE_trans (covector_rankOne_bound G hG c) (hermLE_scalar_mono G hG.posSemidef hc)

end Yau.F04Proof

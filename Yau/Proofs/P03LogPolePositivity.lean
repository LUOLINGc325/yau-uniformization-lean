import Yau.Proofs.P03LogPoleLevi
import Yau.Proofs.P03ComplexRealInner

open scoped Topology ContDiff Matrix ComplexOrder

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.LeafProofs.L22Aux

/-- The exact logarithmic Hessian and complex Cauchy--Schwarz give a positive
lower bound for every regularization parameter. -/
theorem modelLogPole_complexLevi_lower {n : ℕ} (a z v : ComplexVector n)
    {ε : ℝ} (hε : 0 < ε) :
    ε * ‖v‖ ^ 2 / (‖z - a‖ ^ 2 + ε) ^ 2 ≤
      complexLeviQuadratic (modelLogPole a ε) z v := by
  rw [modelLogPole_complexLevi a z v hε]
  let q := ‖z - a‖ ^ 2 + ε
  have hq : 0 < q := add_pos_of_nonneg_of_pos (sq_nonneg _) hε
  have he : ‖v‖ ^ 2 / q -
      ((inner ℝ (z - a) v) ^ 2 + (inner ℝ (z - a) (Complex.I • v)) ^ 2) / q ^ 2 =
      (q * ‖v‖ ^ 2 -
        ((inner ℝ (z - a) v) ^ 2 + (inner ℝ (z - a) (Complex.I • v)) ^ 2)) / q ^ 2 := by
    field_simp
    <;> ring
  change ε * ‖v‖ ^ 2 / q ^ 2 ≤ _
  rw [he]
  apply div_le_div_of_nonneg_right _ (sq_nonneg q)
  have hcs := complexVector_inner_line_bound (z - a) v
  dsimp only [q]
  nlinarith

theorem modelLogPole_leviC_posDef {n : ℕ} (a z : ComplexVector n)
    {ε : ℝ} (hε : 0 < ε) : (leviC (modelLogPole a ε) z).PosDef := by
  apply (leviC_posDef_iff ((modelLogPole_contDiff a hε).contDiffAt.of_le (by simp))).mpr
  intro v hv
  have hq : 0 < ‖z - a‖ ^ 2 + ε := add_pos_of_nonneg_of_pos (sq_nonneg _) hε
  exact (div_pos (mul_pos hε (sq_pos_of_pos (norm_pos_iff.mpr hv)))
    (sq_pos_of_pos hq)).trans_le (modelLogPole_complexLevi_lower a z v hε)

theorem modelLogPole_complexLevi_nonneg {n : ℕ} (a z v : ComplexVector n)
    {ε : ℝ} (hε : 0 < ε) : 0 ≤ complexLeviQuadratic (modelLogPole a ε) z v :=
  (div_nonneg (mul_nonneg hε.le (sq_nonneg _)) (sq_nonneg _)).trans
    (modelLogPole_complexLevi_lower a z v hε)

end Yau.NodeProofs.P03Aux

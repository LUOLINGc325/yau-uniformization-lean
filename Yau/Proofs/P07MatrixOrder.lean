import Yau.Proofs.P07Matrix
import Yau.Blueprint.HeatSmoothing

/-! Directional descriptions of the original Hermitian order. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.P07Aux
open Yau Yau.Blueprint
variable {n : ℕ}

theorem leviDirection_sub (A B : Matrix (Fin n) (Fin n) ℂ) (v : ComplexVector n) :
    leviDirection (A - B) v = leviDirection A v - leviDirection B v := by
  simp only [leviDirection, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]

theorem leviDirection_real_smul (a : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) (v : ComplexVector n) :
    leviDirection ((a : ℂ) • A) v = a * leviDirection A v := by
  simp only [leviDirection, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem hermLE_iff_directional (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    HermLE A B ↔ ∀ v : ComplexVector n, leviDirection A v ≤ leviDirection B v := by
  constructor
  · intro h v
    have hp := (Complex.nonneg_iff.mp (h.dotProduct_mulVec_nonneg (WithLp.ofLp v))).1
    have he := leviDirection_sub B A v
    change 0 ≤ leviDirection (B - A) v at hp
    rw [he] at hp
    linarith
  · intro h
    have hH := hB.sub hA
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
    intro v
    apply Complex.nonneg_iff.mpr
    refine ⟨?_, (hH.im_star_dotProduct_mulVec_self v).symm⟩
    have hp := sub_nonneg.mpr (h (WithLp.toLp 2 v))
    rw [← leviDirection_sub] at hp
    simpa only [leviDirection, WithLp.ofLp_toLp] using hp

theorem hermitian_bounds_iff_abs_directional
    (H B : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (hB : B.IsHermitian) (C : ℝ) :
    (HermLE ((-C : ℂ) • H) B ∧ HermLE B ((C : ℂ) • H)) ↔
      ∀ v : ComplexVector n, |leviDirection B v| ≤ C * leviDirection H v := by
  rw [hermLE_iff_directional _ _ (hH.smul (by simp [IsSelfAdjoint])) hB,
    hermLE_iff_directional _ _ hB (hH.smul (by simp [IsSelfAdjoint]))]
  simp only [← Complex.ofReal_neg, leviDirection_real_smul, neg_mul]
  constructor
  · intro h v
    exact abs_le.mpr ⟨h.1 v, h.2 v⟩
  · intro h
    exact ⟨fun v => (abs_le.mp (h v)).1, fun v => (abs_le.mp (h v)).2⟩

theorem relative_abs_directional_of_upper_and_trace
    (H B : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) (hB : B.IsHermitian)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hupper : HermLE B ((a : ℂ) • H)) (htrace : -b ≤ traceWith H B) :
    ∀ v : ComplexVector n, |leviDirection B v| ≤
      (((n : ℝ) + 1) * a + b) * leviDirection H v := by
  have hlo := relative_lower_bound_of_upper_and_trace H B hH ha hupper htrace
  have hhd := (hermLE_iff_directional _ _ hB
    (hH.isHermitian.smul (by simp [IsSelfAdjoint]))).mp hupper
  have hld := (hermLE_iff_directional _ _
    (hH.isHermitian.smul (by simp [IsSelfAdjoint])) hB).mp hlo
  intro v
  have hh : 0 ≤ leviDirection H v :=
    (Complex.nonneg_iff.mp (hH.posSemidef.dotProduct_mulVec_nonneg (WithLp.ofLp v))).1
  have hhi := hhd v
  have hli := hld v
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_neg,
    leviDirection_real_smul, neg_mul] at hhi hli
  have haH := mul_nonneg ha hh
  have hnbH := mul_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg n) ha) hb) hh
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

end Yau.NodeProofs.P07Aux

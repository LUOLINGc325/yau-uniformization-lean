import Yau.Proofs.F04SourcePositive

open scoped Matrix ComplexOrder

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

theorem hermLE_trans {n : ℕ} {A B C : Herm n} (hAB : HermLE A B) (hBC : HermLE B C) :
    HermLE A C := by
  change (C - A).PosSemidef
  rw [show C - A = (C - B) + (B - A) by abel]
  exact (show (C - B).PosSemidef from hBC).add (show (B - A).PosSemidef from hAB)

theorem hermLE_add {n : ℕ} {A B C D : Herm n} (hAB : HermLE A B) (hCD : HermLE C D) :
    HermLE (A + C) (B + D) := by
  change ((B + D) - (A + C)).PosSemidef
  rw [show (B + D) - (A + C) = (B - A) + (D - C) by abel]
  exact (show (B - A).PosSemidef from hAB).add (show (D - C).PosSemidef from hCD)

theorem hermLE_neg {n : ℕ} {A B : Herm n} (hAB : HermLE A B) : HermLE (-B) (-A) := by
  change (-A - -B).PosSemidef
  rw [show -A - -B = B - A by abel]
  exact hAB

theorem hermLE_real_smul {n : ℕ} {A B : Herm n} {r : ℝ} (hr : 0 ≤ r) (hAB : HermLE A B) :
    HermLE ((r : ℂ) • A) ((r : ℂ) • B) := by
  change ((r : ℂ) • B - (r : ℂ) • A).PosSemidef
  rw [← smul_sub]
  exact (show (B - A).PosSemidef from hAB).smul (Complex.nonneg_iff.mpr ⟨hr, rfl⟩)

theorem hermLE_scalar_mono {n : ℕ} (G : Herm n) (hG : G.PosSemidef) {a b : ℝ} (hab : a ≤ b) :
    HermLE ((a : ℂ) • G) ((b : ℂ) • G) := by
  change ((b : ℂ) • G - (a : ℂ) • G).PosSemidef
  rw [← sub_smul, ← Complex.ofReal_sub]
  exact hG.smul (Complex.nonneg_iff.mpr ⟨sub_nonneg.mpr hab, rfl⟩)

end Yau.F04Proof

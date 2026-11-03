import Yau.Proofs.C02CurvatureCone

/-! The coefficient cone is expressed by genuine scalar quadratic
inequalities. Its trace is strictly positive away from the zero tensor. -/

noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.Blueprint.C02Proof
variable {n : ℕ}

def CurvaturePositive (C : CurvatureArray n) : Prop :=
  (∀ i j k l, star (C j i l k) = C i j k l) ∧
    ∀ v w : Fin n → ℂ, 0 ≤ (star w ⬝ᵥ (curvaturePartial C v *ᵥ w)).re

def curvatureTrace (C : CurvatureArray n) : ℝ := (curvatureRicciPartial C).trace.re

theorem curvaturePartial_isHermitian (C : CurvatureArray n)
    (hC : ∀ i j k l, star (C j i l k) = C i j k l) (v : Fin n → ℂ) :
    (curvaturePartial C v).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [curvaturePartial, star_sum, star_mul, star_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [hC i j k l]
  ring

theorem CurvaturePositive.partial_posSemidef {C : CurvatureArray n}
    (hC : CurvaturePositive C) (v : Fin n → ℂ) : (curvaturePartial C v).PosSemidef := by
  have hH := curvaturePartial_isHermitian C hC.1 v
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro w
  exact Complex.nonneg_iff.mpr ⟨hC.2 v w, (hH.im_star_dotProduct_mulVec_self w).symm⟩

theorem CurvaturePositive.trace_nonneg {C : CurvatureArray n}
    (hC : CurvaturePositive C) : 0 ≤ curvatureTrace C :=
  (Complex.nonneg_iff.mp
    (curvatureRicciPartial_posSemidef C hC.1 hC.partial_posSemidef).trace_nonneg).1

theorem CurvaturePositive.eq_zero_of_trace_zero {C : CurvatureArray n}
    (hC : CurvaturePositive C) (hTrace : curvatureTrace C = 0) : C = 0 := by
  apply curvatureArray_eq_zero_of_trace_zero C hC.1 hC.partial_posSemidef
  apply Complex.ext
  · exact hTrace
  · exact (Complex.nonneg_iff.mp
      (curvatureRicciPartial_posSemidef C hC.1 hC.partial_posSemidef).trace_nonneg).2.symm

theorem CurvaturePositive.trace_pos {C : CurvatureArray n}
    (hC : CurvaturePositive C) (hCne : C ≠ 0) : 0 < curvatureTrace C := by
  have hne : curvatureTrace C ≠ 0 := fun hz => hCne (hC.eq_zero_of_trace_zero hz)
  exact lt_of_le_of_ne hC.trace_nonneg hne.symm

end Yau.Blueprint.C02Proof

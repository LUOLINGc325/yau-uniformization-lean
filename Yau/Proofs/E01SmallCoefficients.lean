import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! Repetition makes every positive conic coefficient arbitrarily small. -/

noncomputable section

namespace Yau.NodeProofs.E01Aux

theorem split_positive_conic_coefficients
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {m : ℕ} (η : Fin m → E) (α : Fin m → ℝ) (hα : ∀ i, 0 < α i)
    (T : ℝ) (hsum : ∑ i, α i = T) (ε : ℝ) (hε : 0 < ε) :
    ∃ (m' : ℕ) (index : Fin m' → Fin m) (β : Fin m' → ℝ),
      (∀ j, 0 < β j ∧ β j ≤ ε) ∧
      (∑ j, β j • η (index j)) = ∑ i, α i • η i ∧ ∑ j, β j = T := by
  classical
  obtain ⟨R, hR⟩ := exists_nat_gt (max (T / ε) 0)
  have hRpos : 0 < (R : ℝ) := (le_max_right _ _).trans_lt hR
  have hTR : T / (R : ℝ) < ε := by
    apply (div_lt_iff₀ hRpos).mpr
    simpa only [mul_comm] using
      (div_lt_iff₀ hε).mp ((le_max_left _ _).trans_lt hR)
  have hαT (i : Fin m) : α i ≤ T :=
    (Finset.single_le_sum (fun j _ => (hα j).le) (Finset.mem_univ i)).trans_eq hsum
  let ι := Fin m × Fin R
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hblock (i : Fin m) : ∑ _j : Fin R, α i / (R : ℝ) = α i := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [div_eq_mul_inv, mul_left_comm, mul_inv_cancel₀ hRpos.ne', mul_one]
  refine ⟨Fintype.card ι, (fun j => (e j).1), (fun j => α (e j).1 / (R : ℝ)), ?_, ?_, ?_⟩
  · intro j
    exact ⟨div_pos (hα _) hRpos,
      (div_le_div_of_nonneg_right (hαT _) hRpos.le).trans hTR.le⟩
  · calc
      ∑ j, (α (e j).1 / (R : ℝ)) • η (e j).1 =
          ∑ p : ι, (α p.1 / (R : ℝ)) • η p.1 :=
        e.sum_comp (fun p : ι => (α p.1 / (R : ℝ)) • η p.1)
      _ = ∑ i : Fin m, ∑ _j : Fin R, (α i / (R : ℝ)) • η i := Fintype.sum_prod_type _
      _ = ∑ i, α i • η i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_smul, hblock]
  · calc
      ∑ j, α (e j).1 / (R : ℝ) = ∑ p : ι, α p.1 / (R : ℝ) :=
        e.sum_comp (fun p : ι => α p.1 / (R : ℝ))
      _ = ∑ i : Fin m, ∑ _j : Fin R, α i / (R : ℝ) := Fintype.sum_prod_type _
      _ = ∑ i, α i := by simp only [hblock]
      _ = T := hsum

end Yau.NodeProofs.E01Aux

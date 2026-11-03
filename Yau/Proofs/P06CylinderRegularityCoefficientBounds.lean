import Yau.Proofs.P06CylinderRegularityMatrixBounds

/-! Numerical bounds on fixed finite coefficient families, chosen before
the solution. No solution norm is used to select these constants. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau.Parabolic

theorem finite_global_abs_bound {E γ : Type*} [TopologicalSpace E] [Fintype γ]
    (f : γ → E → ℝ) (hf : ∀ c, Continuous (f c))
    (hcf : ∀ c, HasCompactSupport (f c)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ c p, |f c p| ≤ B := by
  classical
  have hb (c : γ) : ∃ b : ℝ, ∀ p, |f c p| ≤ b := by
    simpa only [Real.norm_eq_abs] using (hf c).bounded_above_of_compact_support (hcf c)
  choose b hb using hb
  let B : ℝ := ∑ c, max (b c) 0
  refine ⟨B, Finset.sum_nonneg (fun c _ => le_max_right _ _), ?_⟩
  intro c p
  exact (hb c p).trans ((le_max_left (b c) 0).trans
    (Finset.single_le_sum (fun d _ => le_max_right (b d) 0) (Finset.mem_univ c)))

theorem quadratic_upper_bound {ι : Type*} [Fintype ι] (a : ι → ι → ℝ)
    {A : ℝ} (hA : 0 ≤ A) (ha : ∀ i j, |a i j| ≤ A) (v : ι → ℝ) :
    (∑ i, ∑ j, a i j * v i * v j) ≤ (Fintype.card ι : ℝ) * A * ∑ i, (v i)^2 := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ι => (1 : ℝ))
    (fun i => |v i|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, sq_abs] at hCS
  calc
    _ ≤ ∑ i, ∑ j, A * |v i| * |v j| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ |a i j * v i * v j| := le_abs_self _
        _ = |a i j| * |v i| * |v j| := by rw [abs_mul, abs_mul]
        _ ≤ _ := by gcongr; exact ha i j
    _ = A * (∑ i, |v i|)^2 := by
      simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ A * ((Fintype.card ι : ℝ) * ∑ i, (v i)^2) :=
      mul_le_mul_of_nonneg_left hCS hA
    _ = _ := by ring

end Yau.NodeProofs.P06Aux.CylinderReg

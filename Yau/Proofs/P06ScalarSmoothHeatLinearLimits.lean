import Yau.Proofs.P06ScalarSmoothHeatTensorLimits

/-! Fixed finite linear combinations retain uniform convergence of
the complete actual spatial derivative tensors. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.ScalarSmooth

theorem iteratedFDeriv_uniform_small_sum {E α : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype α]
    (F : α → ℝ → E → ℝ) (a : α → ℝ)
    (hF : ∀ c t, 0 < t → ContDiff ℝ ∞ (F c t)) (j : ℕ)
    (hj : ∀ c, ∀ ε : ℝ, 0 < ε → ∃ τ > 0,
      ∀ t, 0 < t → t < τ → ∀ z, ‖iteratedFDeriv ℝ j (F c t) z‖ < ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ τ > 0, ∀ t, 0 < t → t < τ → ∀ z,
      ‖iteratedFDeriv ℝ j (fun y => ∑ c, a c * F c t y) z‖ < ε := by
  classical
  let C : ℝ := (∑ c, |a c|) + 1
  have hS : 0 ≤ ∑ c, |a c| := Finset.sum_nonneg (fun c _ => abs_nonneg _)
  have hC : 0 < C := by dsimp only [C]; linarith
  have hδ : 0 < ε / C := div_pos hε hC
  have hc (c : α) : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∀ z, ‖iteratedFDeriv ℝ j (F c t) z‖ < ε/C := by
    obtain ⟨τ,hτ,hh⟩ := hj c (ε/C) hδ
    filter_upwards [Ioo_mem_nhdsGT hτ] with t ht
    exact hh t ht.1 ht.2
  obtain ⟨τ,hτ,hh⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (eventually_all.mpr hc)
  refine ⟨τ,hτ,?_⟩
  intro t ht htτ z
  have he : iteratedFDeriv ℝ j (fun y => ∑ c, a c * F c t y) z =
      ∑ c, a c • iteratedFDeriv ℝ j (F c t) z := by
    rw [iteratedFDeriv_fun_sum_apply (fun c _ =>
      ((contDiff_const.mul (hF c t ht)).of_le (show (j : ℕ∞ω) ≤ ∞ by simp)).contDiffAt)]
    apply Finset.sum_congr rfl
    intro c _
    exact iteratedFDeriv_const_smul_apply' (a := a c) (f := F c t)
      (((hF c t ht).of_le (show (j : ℕ∞ω) ≤ ∞ by simp)).contDiffAt)
  calc
    _ = ‖∑ c, a c • iteratedFDeriv ℝ j (F c t) z‖ := congrArg norm he
    _ ≤ ∑ c, ‖a c • iteratedFDeriv ℝ j (F c t) z‖ := norm_sum_le _ _
    _ = ∑ c, |a c| * ‖iteratedFDeriv ℝ j (F c t) z‖ := by
      simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ ∑ c, |a c| * (ε/C) := Finset.sum_le_sum (fun c _ =>
      mul_le_mul_of_nonneg_left (hh ⟨ht,htτ⟩ c z).le (abs_nonneg _))
    _ = (∑ c, |a c|) * (ε/C) := (Finset.sum_mul _ _ _).symm
    _ < C * (ε/C) := mul_lt_mul_of_pos_right (by dsimp only [C]; linarith) hδ
    _ = ε := mul_div_cancel₀ _ hC.ne'

end Yau.NodeProofs.P06Aux.ScalarSmooth

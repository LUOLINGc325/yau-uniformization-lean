import Yau.Proofs.D06SourceSymbol
import Yau.Proofs.D06CircleDifferences
import Yau.Proofs.D06MeasurableEnergy

/-! The original smooth periodic source has a quadratic translation difference
bound. Its auxiliary constant is used only for the first W¹ regularity step. -/

open scoped Topology ContDiff
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

open Yau.Blueprint

theorem periodic_deriv_real_complex (f : ℝ → ℂ) (T : ℝ)
    (hp : Function.Periodic f T) (hd : Differentiable ℝ f) :
    Function.Periodic (deriv f) T := by
  intro t
  have heq : (fun x => f (x + T)) = f := funext hp
  have ha : HasDerivAt (fun x : ℝ => x + T) 1 t := by
    simpa only [id_eq] using (hasDerivAt_id t).add_const T
  have h := ((hd (t + T)).hasDerivAt.scomp t ha).deriv
  simpa only [heq, one_smul, Function.comp_def] using h.symm

theorem periodic_smooth_difference_bound (f : ℝ → ℂ)
    (hp : Function.Periodic f (2 * Real.pi)) (hs : ContDiff ℝ ∞ f) :
    ∃ C : ℝ, 0 < C ∧ ∀ t θ : ℝ, ‖f (t + θ) - f t‖ ≤ C * |θ| := by
  have hd : Differentiable ℝ f := hs.differentiable (by simp)
  have hdp := periodic_deriv_real_complex f (2 * Real.pi) hp hd
  have hb := hdp.isBounded_of_continuous (by positivity : 2 * Real.pi ≠ 0)
    (hs.continuous_deriv (by simp))
  obtain ⟨C, hC, hbound⟩ := hb.exists_pos_norm_le
  refine ⟨C, hC, ?_⟩
  intro t θ
  have h := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => hd x) (fun x _ => hbound _ (Set.mem_range_self x))
    (Set.mem_univ t) (Set.mem_univ (t + θ))
  simpa only [add_sub_cancel_left, Real.norm_eq_abs] using h

variable {r : ℕ}

theorem smooth_periodic_matrix_difference_bound (L : ℝ → Matrix (Fin r) (Fin r) ℂ)
    (hp : Function.Periodic L (2 * Real.pi)) (hs : ∀ i j, ContDiff ℝ ∞ (fun t => L t i j)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t θ : ℝ, frobSq (L (t + θ) - L t) ≤ C * θ ^ 2 := by
  have hentry (i j : Fin r) : ∃ C : ℝ, 0 < C ∧ ∀ t θ : ℝ,
      ‖L (t + θ) i j - L t i j‖ ≤ C * |θ| :=
    periodic_smooth_difference_bound _ (fun t => congrArg (fun A => A i j) (hp t)) (hs i j)
  choose C hC hbound using hentry
  refine ⟨∑ i : Fin r, ∑ j : Fin r, C i j ^ 2, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  · intro t θ
    simp only [frobSq, Matrix.sub_apply, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have h := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (hC i j).le (abs_nonneg θ))).mpr (hbound i j t θ)
    simpa only [mul_pow, sq_abs] using h

theorem periodicSymbol_circleDifference_quadratic (L : ℝ → Matrix (Fin r) (Fin r) ℂ)
    (hp : Function.Periodic L (2 * Real.pi)) (hs : ∀ i j, ContDiff ℝ ∞ (fun t => L t i j)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ,
      circleDifference (periodicSymbol L hp) (θ : HardyCircle) ≤ C * θ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := smooth_periodic_matrix_difference_bound L hp hs
  refine ⟨C, hC, ?_⟩
  intro θ
  let A := periodicSymbol L hp
  have hLp := circleMatrix_entries_memLp_top A (periodicSymbol_continuous_of_smooth L hp hs)
  have hD : Integrable (fun t => frobSq (A (t + (θ : HardyCircle)) - A t)) hardyCircleMeasure :=
    matrix_frobSq_integrable _ (fun i j => (((hLp i j).comp_measurePreserving
      (measurePreserving_add_right hardyCircleMeasure (θ : HardyCircle))).sub (hLp i j)).mono_exponent le_top)
  have hpnt (t : HardyCircle) : frobSq (A (t + (θ : HardyCircle)) - A t) ≤ C * θ ^ 2 := by
    induction t using Quotient.inductionOn with
    | h t =>
      rw [← QuotientAddGroup.mk_add]
      exact hbound t θ
  have h := integral_mono_ae hD (integrable_const (C * θ ^ 2)) (ae_of_all _ hpnt)
  have hc : (∫ _ : HardyCircle, C * θ ^ 2 ∂hardyCircleMeasure) = C * θ ^ 2 := by simp
  exact h.trans_eq hc

end Yau.NodeProofs.D06Aux

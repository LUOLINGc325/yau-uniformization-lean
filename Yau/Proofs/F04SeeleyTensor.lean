import Yau.Proofs.F04SeeleyInfiniteMoments

/-! Tensor pullback estimates and all mixed reflection moments. -/

open Filter
open scoped Topology

noncomputable section
set_option maxHeartbeats 1000000

namespace Yau.F04Proof.Seeley

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

abbrev Jet (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (m : ℕ) :=
  ContinuousMultilinearMap ℝ (fun _ : Fin m => E × ℝ) F

def reflectLinear (k : ℕ) : (E × ℝ) →L[ℝ] (E × ℝ) :=
  (ContinuousLinearMap.fst ℝ E ℝ).prod
    ((-dyadic k) • ContinuousLinearMap.snd ℝ E ℝ)

theorem reflectLinear_apply (k : ℕ) (p : E × ℝ) :
    reflectLinear k p = (p.1, -dyadic k * p.2) := rfl

theorem reflectLinear_norm_le (k : ℕ) : ‖reflectLinear (E := E) k‖ ≤ dyadic k := by
  apply (reflectLinear (E := E) k).opNorm_le_bound (dyadic_pos k).le
  intro p
  rw [reflectLinear_apply, Prod.norm_def]
  apply max_le
  · exact (norm_fst_le p).trans
      (le_mul_of_one_le_left (norm_nonneg p) (dyadic_ge_one k))
  · rw [norm_mul, Real.norm_eq_abs, abs_neg, abs_of_pos (dyadic_pos k)]
    exact mul_le_mul_of_nonneg_left (norm_snd_le p) (dyadic_pos k).le

omit [CompleteSpace F] in
theorem tensor_pullback_norm_le (m k : ℕ) (A : Jet E F m) :
    ‖A.compContinuousLinearMap (fun _ : Fin m => reflectLinear k)‖ ≤
      ‖A‖ * dyadic k ^ m := by
  calc
    _ ≤ ‖A‖ * ∏ _i : Fin m, ‖reflectLinear (E := E) k‖ :=
      A.norm_compContinuousLinearMap_le _
    _ ≤ ‖A‖ * ∏ _i : Fin m, dyadic k := by
      exact mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun _ _ => reflectLinear_norm_le k))
        (norm_nonneg A)
    _ = _ := by simp

theorem tensor_moment_summable (m q : ℕ) (A : Jet E F m) :
    Summable (fun k => (seeleyWeight k * (-dyadic k) ^ q) •
      A.compContinuousLinearMap (fun _ : Fin m => reflectLinear k)) := by
  apply ((seeleyWeight_summable (q + m)).mul_right ‖A‖).of_norm_bounded
  intro k
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_of_pos (dyadic_pos k)]
  calc
    _ ≤ (|seeleyWeight k| * dyadic k ^ q) * (‖A‖ * dyadic k ^ m) :=
      mul_le_mul_of_nonneg_left (tensor_pullback_norm_le m k A)
        (mul_nonneg (abs_nonneg _) (pow_nonneg (dyadic_pos k).le _))
    _ = (|seeleyWeight k| * dyadic k ^ (q + m)) * ‖A‖ := by rw [pow_add]; ring

end Yau.F04Proof.Seeley

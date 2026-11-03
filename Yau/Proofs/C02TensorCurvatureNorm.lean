import Yau.LeafProofs.L23TensorMultilinear
import Mathlib.Analysis.InnerProductSpace.Dual

/-! Passing from a fully covariant tensor bound to the operator norm of
its metric-dual curvature action, with no dimension factor. -/

noncomputable section
open scoped InnerProductSpace
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local instance tensor_norm_end_group : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance tensor_norm_end_space : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance tensor_norm_one_group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance tensor_norm_one_space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance tensor_norm_two_group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance tensor_norm_two_space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance

theorem curvature_action_norm_le (F : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) (B : E →L[ℝ] E)
    (hpair : ∀ u v w z, ⟪F u v w, z⟫_ℝ = T ![B u, B v, w, z]) :
    ‖F‖ ≤ ‖T‖ * ‖B‖ ^ 2 := by
  have hpoint (u v w : E) : ‖F u v w‖ ≤ ‖T‖ * ‖B‖ ^ 2 * ‖u‖ * ‖v‖ * ‖w‖ := by
    have ht := T.le_opNorm ![B u, B v, w, F u v w]
    rw [← hpair, real_inner_self_eq_norm_sq, Real.norm_of_nonneg (sq_nonneg _)] at ht
    have hprod : ‖T‖ * ∏ i : Fin 4, ‖(![B u, B v, w, F u v w] : Fin 4 → E) i‖ ≤
        (‖T‖ * ‖B‖ ^ 2 * ‖u‖ * ‖v‖ * ‖w‖) * ‖F u v w‖ := by
      simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.prod_univ_zero, mul_one]
      calc
        _ ≤ ‖T‖ * ((‖B‖ * ‖u‖) * ((‖B‖ * ‖v‖) * (‖w‖ * ‖F u v w‖))) := by
          gcongr
          · exact B.le_opNorm u
          · exact B.le_opNorm v
        _ = _ := by ring
    have hs := ht.trans hprod
    have hC : 0 ≤ ‖T‖ * ‖B‖ ^ 2 * ‖u‖ * ‖v‖ * ‖w‖ := by positivity
    by_cases hz : ‖F u v w‖ = 0
    · rw [hz]; exact hC
    · have hp : 0 < ‖F u v w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      nlinarith
  apply F.opNorm_le_bound (by positivity)
  intro u
  apply (F u).opNorm_le_bound (by positivity)
  intro v
  apply (F u v).opNorm_le_bound (by positivity)
  intro w
  simpa only [mul_assoc] using hpoint u v w

end Yau.Blueprint.C02Proof

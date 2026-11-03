import spec.CHAIN.CONTRACTS
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open Set
open scoped Topology
namespace Yau.Blueprint.C02Proof

theorem scalar_exponential_lower_comparison {F D : ℝ → ℝ} {a b C : ℝ}
    (hab : a ≤ b) (hF : ContinuousOn F (Icc a b))
    (hD : ∀ t ∈ Ioo a b, HasDerivAt F (D t) t)
    (hLower : ∀ t ∈ Ioo a b, -C * F t ≤ D t) :
    F a ≤ Real.exp (C * (b - a)) * F b := by
  let G := fun t => Real.exp (C * t) * F t
  let Dg := fun t => Real.exp (C * t) * (C * F t + D t)
  have hG : ContinuousOn G (Icc a b) := (Real.continuous_exp.comp
    (continuous_const.mul continuous_id)).continuousOn.mul hF
  have hGd (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt G (Dg t) t := by
    have he := ((hasDerivAt_id t).const_mul C).exp
    convert he.fun_mul (hD t ht) using 1 <;> dsimp only [G, Dg, id_eq]
    all_goals ring
  have hMon : MonotoneOn G (Icc a b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hG
    · intro t ht
      rw [interior_Icc] at ht
      exact (hGd t ht).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact mul_nonneg (Real.exp_pos _).le (by have hh := hLower t ht; linarith)
  have hh := hMon (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  have hexp : Real.exp (C * b) = Real.exp (C * a) * Real.exp (C * (b - a)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change Real.exp (C * a) * F a ≤ Real.exp (C * b) * F b at hh
  rw [hexp, mul_assoc] at hh
  exact (mul_le_mul_iff_right₀ (Real.exp_pos _)).mp hh

end Yau.Blueprint.C02Proof

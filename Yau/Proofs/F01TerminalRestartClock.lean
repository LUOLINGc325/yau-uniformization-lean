import Yau.Proofs.F01TerminalRestartPotentialAlgebra

/-! The computed restart correction preserves the actual original
determinant time equation, including its closed time faces. -/
noncomputable section
open Set
open scoped ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem restart_logdet_sum
    (g K : HermitianField M) (h : ℝ → HermitianField M) (h0 : h 0 = K)
    (x : M.Carrier) (s : ℝ) :
    flowLogDetRatio g h x s = flowLogDetRatio K h x s +
      flowLogDetRatio g (fun _ => K) x 0 := by
  have hh := flow_logdet_rebase g h 0 s x
  have heq : flowLogDetRatio K h x s = flowLogDetRatio g h x s -
      flowLogDetRatio g (fun _ => K) x 0 := by
    simpa only [zero_add, h0, flowLogDetRatio] using hh
  linarith

theorem lifted_restart_time_equation
    (g K : HermitianField M) (u : M.Carrier → ℝ)
    (h : ℝ → HermitianField M) (V : M.Carrier → ℝ → ℝ) (h0 : h 0 = K)
    {I : Set ℝ}
    (hV : ∀ x s, s ∈ I → HasDerivWithinAt (V x)
      (flowLogDetRatio K h x s) I s) :
    ∀ x s, s ∈ I → HasDerivWithinAt (liftedRestartPotential g K u V x)
      (flowLogDetRatio g h x s) I s := by
  intro x s hs
  have hLinear : HasDerivWithinAt (fun r : ℝ => r * flowLogDetRatio g (fun _ => K) x 0)
      (flowLogDetRatio g (fun _ => K) x 0) I s := by
    simpa only [id_eq, mul_one, one_mul] using
      ((hasDerivAt_id s).mul_const (flowLogDetRatio g (fun _ => K) x 0)).hasDerivWithinAt
  have hh := ((hV x s hs).const_add (u x)).add hLinear
  rw [← restart_logdet_sum g K h h0 x s] at hh
  exact hh

theorem shifted_lifted_restart_time_equation
    (g K : HermitianField M) (u : M.Carrier → ℝ)
    (h : ℝ → HermitianField M) (V : M.Carrier → ℝ → ℝ) (h0 : h 0 = K)
    {I J : Set ℝ} (T : ℝ) (hMap : MapsTo (fun t : ℝ => t - T) J I)
    (hV : ∀ x s, s ∈ I → HasDerivWithinAt (V x)
      (flowLogDetRatio K h x s) I s) :
    ∀ x t, t ∈ J → HasDerivWithinAt
      (fun r => liftedRestartPotential g K u V x (r - T))
      (flowLogDetRatio g h x (t - T)) J t := by
  intro x t ht
  have hClock : HasDerivWithinAt (fun r : ℝ => r - T) 1 J t :=
    ((hasDerivAt_id t).sub_const T).hasDerivWithinAt
  simpa only [Function.comp_def, mul_one] using
    (lifted_restart_time_equation g K u h V h0 hV x (t - T) (hMap ht)).comp t hClock hMap

end Yau.NodeProofs.F01Aux

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

/-!
A continuous minimum of smooth path lengths can be compared with a scalar
barrier at a negative minimum.  This is the scalar step in the first-exit
argument: the differentiable touching function is the length of the current
minimizing path.  Completeness is not an input.
-/

noncomputable section

open scoped Topology

namespace Yau.NodeProofs.C01Aux

/-- A negative minimum of `l - b` is also a minimum of `f - b` when `f`
is an upper touching path-length function. -/
theorem upperTouch_sub_localMin
    {l b f : ℝ → ℝ} {s : Set ℝ} {t : ℝ}
    (hmin : IsMinOn (fun u => l u - b u) s t)
    (htouch : f t = l t) (hupper : ∀ u ∈ s, l u ≤ f u) :
    IsMinOn (fun u => f u - b u) s t := by
  intro u hu
  change f t - b t ≤ f u - b u
  rw [htouch]
  exact (hmin hu).trans (sub_le_sub_right (hupper u hu) (b u))

/-- At an interior negative minimum, a differential lower bound for a
current minimizing path contradicts the exact linear barrier equation.
The full geometric argument supplies `f` from a genuine first-exit segment. -/
theorem no_negative_localMin_of_upperTouch
    {l b f : ℝ → ℝ} {t a c : ℝ}
    (hmin : IsLocalMin (fun u => l u - b u) t)
    (htouch : f t = l t) (hupper : ∀ᶠ u in 𝓝 t, l u ≤ f u)
    (hfd : HasDerivAt f a t)
    (hbd : HasDerivAt b (-c * (1 + b t)) t)
    (hc : 0 < c) (hbound : -c * (1 + l t) ≤ a) :
    b t ≤ l t := by
  by_contra hfail
  have hlt : l t < b t := lt_of_not_ge hfail
  have hmin' : IsLocalMin (fun u => f u - b u) t := by
    filter_upwards [hmin, hupper] with u hu huf
    change f t - b t ≤ f u - b u
    rw [htouch]
    exact hu.trans (sub_le_sub_right huf (b u))
  have hzero : a - (-c * (1 + b t)) = 0 :=
    hmin'.hasDerivAt_eq_zero (hfd.sub hbd)
  have hgap : 0 < c * (b t - l t) := mul_pos hc (sub_pos.mpr hlt)
  linarith

end Yau.NodeProofs.C01Aux

import Yau.Proofs.C01ExitComparison
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
The scalar comparison in the first-exit argument requires a differentiable
upper touching path length at each time, and continuity of the minimum.
It does not differentiate the minimum or assume a minimizing geodesic in
an already complete positive-time metric.
-/

noncomputable section

open scoped Topology
open Set Filter

namespace Yau.NodeProofs.C01Aux

/-- The same upper-touch comparison works at the final time of a compact
interval: the direction toward its initial time lies in its tangent cone. -/
theorem no_negative_minOn_of_upperTouch
    {l b f : ℝ → ℝ} {s t a d c : ℝ}
    (ht : t ∈ Ioc s a)
    (hmin : IsMinOn (fun u => l u - b u) (Icc s a) t)
    (htouch : f t = l t) (hupper : ∀ u ∈ Icc s a, l u ≤ f u)
    (hfd : HasDerivAt f d t)
    (hbd : HasDerivAt b (-c * (1 + b t)) t)
    (hc : 0 < c) (hbound : -c * (1 + l t) ≤ d) :
    b t ≤ l t := by
  by_contra hfail
  have hlt : l t < b t := lt_of_not_ge hfail
  have hmin' := upperTouch_sub_localMin hmin htouch hupper
  have hleft : s - t ∈ posTangentConeAt (Icc s a) t :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc s a).segment_subset ⟨ht.1.le, ht.2⟩
        ⟨le_rfl, ht.1.le.trans ht.2⟩)
  have hnonneg := hmin'.isLocalMinOn.hasFDerivWithinAt_nonneg
    (hfd.sub hbd).hasFDerivAt.hasFDerivWithinAt hleft
  have hnonneg' : 0 ≤ (s - t) * (d - (-c * (1 + b t))) := by
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] using hnonneg
  have hdiff : 0 < d - (-c * (1 + b t)) := by
    have hgap := mul_pos hc (sub_pos.mpr hlt)
    linarith
  have hneg := mul_neg_of_neg_of_pos (sub_neg.mpr ht.1) hdiff
  exact (not_lt_of_ge hnonneg') hneg

/-- Comparison for a continuous minimum of admissible path lengths.  The
geometric application supplies `f` by the current first-exit minimizer. -/
theorem lower_bound_of_touching_lengths
    (l b c : ℝ → ℝ) {s a : ℝ} (hsa : s ≤ a)
    (hl : ContinuousOn l (Icc s a)) (hb : ContinuousOn b (Icc s a))
    (hstart : b s ≤ l s)
    (hbd : ∀ t ∈ Ioc s a, HasDerivAt b (-c t * (1 + b t)) t)
    (hc : ∀ t ∈ Ioc s a, 0 < c t)
    (hpaths : ∀ t ∈ Ioc s a, ∃ (f : ℝ → ℝ) (d : ℝ),
      f t = l t ∧ (∀ u ∈ Icc s a, l u ≤ f u) ∧
      HasDerivAt f d t ∧ -c t * (1 + l t) ≤ d) :
    ∀ t ∈ Icc s a, b t ≤ l t := by
  intro t ht
  by_contra hfail
  have htneg : l t - b t < 0 := sub_neg.mpr (lt_of_not_ge hfail)
  obtain ⟨v, hv, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hsa) (hl.sub hb)
  have hvneg : l v - b v < 0 := (hmin ht).trans_lt htneg
  have hvs : s < v := by
    by_contra hvs
    have heq : v = s := le_antisymm (le_of_not_gt hvs) hv.1
    subst v
    exact (not_lt_of_ge (sub_nonneg.mpr hstart)) hvneg
  obtain ⟨f, d, htouch, hupper, hfd, hbound⟩ := hpaths v ⟨hvs, hv.2⟩
  have hvbound := no_negative_minOn_of_upperTouch ⟨hvs, hv.2⟩ hmin
    htouch hupper hfd (hbd v ⟨hvs, hv.2⟩) (hc v ⟨hvs, hv.2⟩) hbound
  exact (not_lt_of_ge (sub_nonneg.mpr hvbound)) hvneg

/-- The precise square-root-time barrier appearing in charts.tex.  Its
derivative is only required for positive times. -/
theorem exitExponential_hasDerivAt (L C : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u => (1 + L) * Real.exp (-2 * C * Real.sqrt u) - 1)
      (-(C / Real.sqrt t) *
        (1 + ((1 + L) * Real.exp (-2 * C * Real.sqrt t) - 1))) t := by
  have hroot : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht)
  convert (((Real.hasDerivAt_sqrt ht.ne').const_mul (-2 * C)).exp.const_mul (1 + L)).sub_const 1 using 1
  field_simp [hroot]
  <;> ring

end Yau.NodeProofs.C01Aux

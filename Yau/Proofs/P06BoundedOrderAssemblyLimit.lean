import Yau.Proofs.P06TimeIntegralPotentialEvolution

/-! Finite pointwise limits and closed order cones for the original smooth limit.
These lemmas require no heat class, global L² bound, or cutoff construction. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.P06Aux.BoundedOrder
open Yau Yau.Blueprint
variable {n : ℕ} {M : ComplexManifold n}

theorem formComponents_tendsto_of_localSmoothLimit
    (Us : ℕ → ℝ → RealForm M 2) (U : ℝ → RealForm M 2)
    (hlim : FormHeatLocalSmoothLimit Us U) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (I : Fin 2 → RIdx n)
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun j => formComponents (Us j t) x z I) atTop (𝓝 (formComponents (U t) x z I)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨J, hJ⟩ := hlim x {z} isCompact_singleton
    (by intro w hw; simpa only [mem_singleton_iff.mp hw] using hz)
    (t / 2) (t + 1) (by positivity) (by linarith) 0 I ε hε
  refine ⟨J, fun j hj => ?_⟩
  have hh := hJ j hj z (mem_singleton z) t ⟨by linarith, by linarith⟩
  simpa only [norm_iteratedFDeriv_zero, Real.dist_eq, Real.norm_eq_abs] using hh

theorem formHermitianMatrix_tendsto_of_localSmoothLimit
    (Us : ℕ → ℝ → RealForm M 2) (U : ℝ → RealForm M 2)
    (hlim : FormHeatLocalSmoothLimit Us U) (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun j => formHermitianMatrix (Us j t) x) atTop (𝓝 (formHermitianMatrix (U t) x)) := by
  apply tendsto_pi_nhds.mpr
  intro a
  apply tendsto_pi_nhds.mpr
  intro b
  have h₁ := formComponents_tendsto_of_localSmoothLimit Us U hlim x
    (mem_extChartAt_target x) ![(a, 0), (b, 1)] ht
  have h₂ := formComponents_tendsto_of_localSmoothLimit Us U hlim x
    (mem_extChartAt_target x) ![(a, 0), (b, 0)] ht
  simpa only [TimePotential.formHermitianMatrix_components, Function.comp_def, chartPt] using
    (((Complex.continuous_ofReal.tendsto _).comp h₁).add
      (((Complex.continuous_ofReal.tendsto _).comp h₂).const_mul Complex.I)).div_const 2

theorem formNormSq_tendsto_of_localSmoothLimit
    (g : HermitianField M) (Us : ℕ → ℝ → RealForm M 2) (U : ℝ → RealForm M 2)
    (hlim : FormHeatLocalSmoothLimit Us U) (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun j => formNormSq g (Us j t) x) atTop (𝓝 (formNormSq g (U t) x)) := by
  unfold formNormSq formInner
  apply tendsto_const_nhds.mul
  apply tendsto_finset_sum
  intro I hI
  apply tendsto_finset_sum
  intro J hJ
  exact ((formComponents_tendsto_of_localSmoothLimit Us U hlim x (mem_extChartAt_target x) I ht).mul
    (formComponents_tendsto_of_localSmoothLimit Us U hlim x (mem_extChartAt_target x) J ht)).mul_const _

theorem formNormSq_bound_of_localSmoothLimit
    (g : HermitianField M) (B : ℝ) (Us : ℕ → ℝ → RealForm M 2) (U : ℝ → RealForm M 2)
    (hlim : FormHeatLocalSmoothLimit Us U)
    (hbound : ∀ j, 1 ≤ j → ∀ t, 0 < t → ∀ x, formNormSq g (Us j t) x ≤ B) :
    ∀ t, 0 < t → ∀ x, formNormSq g (U t) x ≤ B := by
  intro t ht x
  apply le_of_tendsto (formNormSq_tendsto_of_localSmoothLimit g Us U hlim x ht)
  filter_upwards [eventually_ge_atTop 1] with j hj
  exact hbound j hj t ht x

theorem formOrderBound_of_localSmoothLimit
    (g : HermitianField M) (C : ℝ) (Us : ℕ → ℝ → RealForm M 2)
    (U : ℝ → RealForm M 2) (hlim : FormHeatLocalSmoothLimit Us U)
    (hbound : ∀ j, 1 ≤ j → ∀ t, 0 < t → FormOrderBound g C (Us j t)) :
    ∀ t, 0 < t → FormOrderBound g C (U t) := by
  intro t ht x
  have hm := formHermitianMatrix_tendsto_of_localSmoothLimit Us U hlim x ht
  constructor
  · apply Matrix.posSemidef_is_closed.mem_of_tendsto (hm.sub tendsto_const_nhds)
    filter_upwards [eventually_ge_atTop 1] with j hj
    exact (hbound j hj t ht x).1
  · apply Matrix.posSemidef_is_closed.mem_of_tendsto (tendsto_const_nhds.sub hm)
    filter_upwards [eventually_ge_atTop 1] with j hj
    exact (hbound j hj t ht x).2

theorem formLE_of_localSmoothLimits
    (Us Vs : ℕ → ℝ → RealForm M 2) (U V : ℝ → RealForm M 2)
    (hU : FormHeatLocalSmoothLimit Us U) (hV : FormHeatLocalSmoothLimit Vs V)
    (horder : ∀ j, 1 ≤ j → ∀ t, 0 < t → FormLE (Us j t) (Vs j t)) :
    ∀ t, 0 < t → FormLE (U t) (V t) := by
  intro t ht x
  apply Matrix.posSemidef_is_closed.mem_of_tendsto
    ((formHermitianMatrix_tendsto_of_localSmoothLimit Vs V hV x ht).sub
      (formHermitianMatrix_tendsto_of_localSmoothLimit Us U hU x ht))
  filter_upwards [eventually_ge_atTop 1] with j hj
  exact horder j hj t ht x

end Yau.NodeProofs.P06Aux.BoundedOrder

import Yau.LeafProofs.L12Geodesic

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal Matrix ContDiff
namespace Yau.LeafProofs.L12Aux

/-- Nearby initial states admit a common existence interval on which the
solutions remain in a prescribed open set. -/
theorem exists_uniform_local_solution_in_open
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E → E} {z₀ : E} {U : Set E}
    (hF : ContDiffAt ℝ 1 F z₀) (hU : IsOpen U) (hz₀ : z₀ ∈ U) :
    ∃ V ∈ 𝓝 z₀, ∃ δ > (0 : ℝ), ∀ z ∈ V, ∃ η : ℝ → E,
      η 0 = z ∧ ∀ t ∈ Set.Ioo (-δ) δ,
        η t ∈ U ∧ HasDerivAt η (F (η t)) t := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hF
  obtain ⟨α, hα, hαcont⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  have hzball : z₀ ∈ Metric.closedBall z₀ (r : ℝ) := Metric.mem_closedBall_self r.coe_nonneg
  have hdomain : Metric.closedBall z₀ (r : ℝ) ×ˢ Set.Icc (-ε) ε ∈ 𝓝 (z₀, (0 : ℝ)) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod (Metric.closedBall_mem_nhds z₀ hr)
      (Icc_mem_nhds (by linarith) hε)
  have hαat : ContinuousAt α (z₀, (0 : ℝ)) := by
    apply hαcont.continuousAt
    simpa only [zero_sub, zero_add] using hdomain
  have hpre : α ⁻¹' U ∈ 𝓝 (z₀, (0 : ℝ)) :=
    hαat.preimage_mem_nhds ((hα z₀ hzball).1.symm ▸ hU.mem_nhds hz₀)
  rw [nhds_prod_eq] at hpre
  obtain ⟨V, hV, J, hJ, hVJ⟩ := Filter.mem_prod_iff.mp hpre
  obtain ⟨ρ, hρ, hρJ⟩ := Metric.mem_nhds_iff.mp hJ
  refine ⟨V ∩ Metric.closedBall z₀ (r : ℝ),
    Filter.inter_mem hV (Metric.closedBall_mem_nhds z₀ hr), min ε ρ,
    lt_min hε hρ, ?_⟩
  intro z hz
  refine ⟨fun t => α (z, t), (hα z hz.2).1, ?_⟩
  intro t ht
  have htε : t ∈ Set.Ioo (-ε) ε :=
    ⟨by linarith [ht.1, min_le_left ε ρ], by linarith [ht.2, min_le_left ε ρ]⟩
  have htρ : t ∈ Metric.ball (0 : ℝ) ρ := by
    rw [Real.ball_eq_Ioo]
    exact ⟨by linarith [ht.1, min_le_right ε ρ], by linarith [ht.2, min_le_right ε ρ]⟩
  refine ⟨hVJ ⟨hz.1, hρJ htρ⟩, ?_⟩
  exact ((hα z hz.2).2 t (by simpa only [zero_sub, zero_add] using Set.Ioo_subset_Icc_self htε)).hasDerivAt
    (by simpa only [zero_sub, zero_add] using Icc_mem_nhds htε.1 htε.2)

section UniformManifoldExistence
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I 1 N]
  [BoundarylessManifold I N] {v : (p : N) → TangentSpace I p}

set_option backward.isDefEq.respectTransparency false in
theorem exists_uniform_local_integral_curves
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun p => (⟨p, v p⟩ : TangentBundle I N))) (p : N) :
    ∃ U ∈ 𝓝 p, ∃ ε > (0 : ℝ), ∀ q ∈ U, ∃ γ : ℝ → N,
      γ 0 = q ∧ IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε) := by
  have hvp := hv p
  rw [contMDiffAt_iff] at hvp
  obtain ⟨_, hvp⟩ := hvp
  have hp : I.IsInteriorPoint p := BoundarylessManifold.isInteriorPoint
  let c := extChartAt I p
  let F : E → E := fun z => tangentCoordChange I (c.symm z) p (c.symm z) (v (c.symm z))
  have hF : ContDiffAt ℝ 1 F (c p) :=
    (hvp.contDiffAt (range_mem_nhds_isInteriorPoint hp)).snd
  obtain ⟨V, hV, ε, hε, hsol⟩ := exists_uniform_local_solution_in_open hF
    isOpen_interior ((I.isInteriorPoint_iff).mp hp)
  refine ⟨c.source ∩ c ⁻¹' V,
    Filter.inter_mem (extChartAt_source_mem_nhds (I := I) p)
      ((continuousAt_extChartAt (I := I) p).preimage_mem_nhds hV), ε, hε, ?_⟩
  intro q hq
  obtain ⟨η, hη0, hη⟩ := hsol (c q) hq.2
  refine ⟨c.symm ∘ η, ?_, ?_⟩
  · rw [Function.comp_apply, hη0]
    exact c.left_inv hq.1
  · intro t ht
    let xt : N := c.symm (η t)
    have h : HasDerivAt η (tangentCoordChange I xt p xt (v xt)) t := (hη t ht).2
    have htarg : η t ∈ c.target := interior_subset (hη t ht).1
    have hft1 : xt ∈ c.source := c.map_target htarg
    have hft2 : xt ∈ (extChartAt I xt).source := mem_extChartAt_source _
    apply HasMFDerivAt.hasMFDerivWithinAt
    refine ⟨(continuousAt_extChartAt_symm'' htarg).comp h.continuousAt,
      HasDerivWithinAt.hasFDerivWithinAt ?_⟩
    simp only [mfld_simps, hasDerivWithinAt_univ]
    change HasDerivAt ((extChartAt I xt ∘ c.symm) ∘ η) (v xt) t
    rw [← tangentCoordChange_self (I := I) (x := xt) (z := xt) (v := v xt) hft2,
      ← tangentCoordChange_comp (x := p) ⟨⟨hft2, hft1⟩, hft2⟩]
    apply HasFDerivAt.comp_hasDerivAt _ _ h
    apply HasFDerivWithinAt.hasFDerivAt (s := Set.range I) _
      (mem_nhds_iff.mpr ⟨interior c.target,
        Set.Subset.trans interior_subset (extChartAt_target_subset_range ..),
        isOpen_interior, (hη t ht).1⟩)
    rw [← c.right_inv htarg]
    exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩

theorem exists_uniform_time_on_compact
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun p => (⟨p, v p⟩ : TangentBundle I N)))
    {K : Set N} (hK : IsCompact K) :
    ∃ ε > (0 : ℝ), ∀ q ∈ K, ∃ γ : ℝ → N,
      γ 0 = q ∧ IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε) := by
  let P : ℝ → N → Prop := fun a q => ∃ γ : ℝ → N,
    γ 0 = q ∧ IsMIntegralCurveOn γ v (Set.Ioo (-a) a)
  have hlocal : ∀ q ∈ K, ∀ᶠ z : ℝ × N in 𝓝 (0, q), P z.1 z.2 := by
    intro q _
    obtain ⟨U, hU, δ, hδ, hsol⟩ := exists_uniform_local_integral_curves hv q
    rw [nhds_prod_eq]
    filter_upwards [Filter.prod_mem_prod (Iio_mem_nhds hδ) hU] with z hz
    obtain ⟨γ, hγ0, hγ⟩ := hsol z.2 hz.2
    exact ⟨γ, hγ0,
      hγ.mono (Set.Ioo_subset_Ioo (neg_le_neg hz.1.le) hz.1.le)⟩
  have hall : ∀ᶠ a in 𝓝 (0 : ℝ), ∀ q ∈ K, P a q :=
    hK.eventually_forall_of_forall_eventually hlocal
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨ρ / 2, half_pos hρ, hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hρ)]
  exact half_lt_self hρ

/-- A smooth vector field admits a global integral curve if all its finite
partial curves from the given point stay in a compact set on every bounded
time interval. -/
theorem exists_global_integral_curve_of_compact_trapping [T2Space N]
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun q => (⟨q, v q⟩ : TangentBundle I N))) (p : N)
    (htrap : ∀ T > (0 : ℝ), ∃ K : Set N, IsCompact K ∧
      ∀ a : ℝ, 0 < a → a ≤ T → ∀ γ : ℝ → N, γ 0 = p →
        IsMIntegralCurveOn γ v (Set.Ioo (-a) a) →
        Set.MapsTo γ (Set.Ioo (-a) a) K) :
    ∃ γ : ℝ → N, γ 0 = p ∧ IsMIntegralCurve γ v := by
  classical
  let S : Set ℝ := {a | ∃ γ : ℝ → N,
    γ 0 = p ∧ IsMIntegralCurveOn γ v (Set.Ioo (-a) a)}
  obtain ⟨ε₀, hε₀, hinit⟩ := exists_uniform_time_on_compact hv
    (isCompact_singleton (x := p))
  have hε₀S : ε₀ ∈ S := hinit p (Set.mem_singleton p)
  suffices hn : ¬ BddAbove S by
    rw [not_bddAbove_iff] at hn
    rw [exists_isMIntegralCurve_iff_exists_isMIntegralCurveOn_Ioo hv]
    intro a
    obtain ⟨b, ⟨γ, hγ0, hγ⟩, hab⟩ := hn a
    exact ⟨γ, hγ0, hγ.mono (Set.Ioo_subset_Ioo (neg_le_neg hab.le) hab.le)⟩
  intro hbdd
  set A := sSup S with hAdef
  have hε₀A : ε₀ ≤ A := le_csSup hbdd hε₀S
  have hA : 0 < A := hε₀.trans_le hε₀A
  obtain ⟨K, hK, htrapK⟩ := htrap A hA
  obtain ⟨δ, hδ, hδsol⟩ := exists_uniform_time_on_compact hv hK
  let ε := min δ ε₀
  have hε : 0 < ε := lt_min hδ hε₀
  have hεA : ε ≤ A := (min_le_right δ ε₀).trans hε₀A
  have hsol : ∀ q ∈ K, ∃ γ : ℝ → N,
      γ 0 = q ∧ IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε) := by
    intro q hq
    obtain ⟨γ, hγ0, hγ⟩ := hδsol q hq
    exact ⟨γ, hγ0, hγ.mono
      (Set.Ioo_subset_Ioo (neg_le_neg (min_le_left δ ε₀)) (min_le_left δ ε₀))⟩
  obtain ⟨a, haS, hlt⟩ := Real.add_neg_lt_sSup (⟨ε₀, hε₀S⟩ : S.Nonempty)
    (ε := -(ε / 2)) (by linarith)
  rw [← hAdef, ← sub_eq_add_neg] at hlt
  have haA : a ≤ A := le_csSup hbdd haS
  have ha : 0 < a := by linarith
  obtain ⟨γ, h0, hγ⟩ := haS
  have hγK := htrapK a ha haA γ h0 hγ
  obtain ⟨γ1_aux, h1_aux, hγ1⟩ := hsol (γ (-(A - ε / 2)))
    (hγK ⟨neg_lt_neg hlt, by linarith⟩)
  rw [← isMIntegralCurveOn_comp_add (dt := A - ε / 2)] at hγ1
  set γ1 := γ1_aux ∘ (· + (A - ε / 2)) with γ1_def
  have heq1 : γ1 (-(A - ε / 2)) = γ (-(A - ε / 2)) := by simp [γ1_def, h1_aux]
  obtain ⟨γ2_aux, h2_aux, hγ2⟩ := hsol (γ (A - ε / 2))
    (hγK ⟨by linarith, hlt⟩)
  rw [← isMIntegralCurveOn_comp_sub (dt := A - ε / 2)] at hγ2
  set γ2 := γ2_aux ∘ (· - (A - ε / 2)) with γ2_def
  have heq2 : γ2 (A - ε / 2) = γ (A - ε / 2) := by simp [γ2_def, h2_aux]
  simp_rw [Set.mem_Ioo, ← sub_lt_iff_lt_add, ← lt_sub_iff_add_lt, ← Set.mem_Ioo] at hγ1
  simp_rw [Set.mem_Ioo, lt_sub_iff_add_lt, sub_lt_iff_lt_add, ← Set.mem_Ioo] at hγ2
  set γext : ℝ → N := Set.piecewise (Set.Ioo (-(A + ε / 2)) a)
    (Set.piecewise (Set.Ioo (-a) a) γ γ1) γ2 with γext_def
  have heqext : γext 0 = p := by
    rw [γext_def, Set.piecewise, ite_eq_left ⟨by linarith, ha⟩,
      Set.piecewise, ite_eq_left ⟨by linarith, ha⟩, h0]
  suffices hext : IsMIntegralCurveOn γext v
      (Set.Ioo (-(A + ε / 2)) (A + ε / 2)) from
    (not_lt.mpr (le_csSup hbdd ⟨γext, heqext, hext⟩))
      (lt_add_of_pos_right A (half_pos hε))
  apply (isMIntegralCurveOn_piecewise (t₀ := A - ε / 2) hv _ hγ2
    ⟨⟨by linarith, hlt⟩, ⟨by linarith, by linarith⟩⟩
    (by rw [Set.piecewise, ite_eq_left ⟨by linarith, hlt⟩, ← heq2])).mono
      (Set.Ioo_subset_Ioo_union_Ioo le_rfl (by linarith) (by linarith))
  exact (isMIntegralCurveOn_piecewise (t₀ := -(A - ε / 2)) hv hγ hγ1
    ⟨⟨neg_lt_neg hlt, by linarith⟩, ⟨by linarith, by linarith⟩⟩ heq1.symm).mono
      (Set.union_comm _ _ ▸ Set.Ioo_subset_Ioo_union_Ioo (by linarith) (by linarith) le_rfl)

end UniformManifoldExistence
end Yau.LeafProofs.L12Aux

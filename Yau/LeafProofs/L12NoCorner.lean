import Yau.LeafProofs.L12NormalCoordinates
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal Matrix ContDiff
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

/-! Local metric comparison with arbitrarily small distortion, and the
no-corner conclusion for two actual radial geodesics. -/

theorem exists_realFrozenChart_ball_of_one_lt (g : SmoothMetric M) (x : M.Carrier)
    {C : ℝ} (hC : 1 < C) :
    letI := manifold_realSmooth M
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    ∃ ρ > (0 : ℝ), Metric.ball (realFrozenChart x x) ρ ⊆ realFrozenChartDomain x ∧
      ∀ v ∈ Metric.ball (realFrozenChart x x) ρ,
        ‖realFrozenTransport g x (realFrozenChartInv x v)‖ < C ∧
        ‖realFrozenTransportBack g x (realFrozenChartInv x v)‖ < C := by
  letI := manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  have hc := (realFrozenChartInv_contMDiffAt g x (realFrozenChart x x)
    (realFrozenChart_self_mem x)).continuousAt
  have he : realFrozenChartInv x (realFrozenChart x x) = x :=
    realFrozenChartInv_realFrozenChart x x (mem_extChartAt_source x)
  have hc' : Tendsto (realFrozenChartInv x) (𝓝 (realFrozenChart x x)) (𝓝 x) := by
    simpa only [ContinuousAt, he] using hc
  have hn := hc'.eventually (realTangent_trivialization_almostIsometry g x hC)
  have ho : realFrozenChartDomain x ∈ 𝓝 (realFrozenChart x x) :=
    (realFrozenChartDomain_isOpen x).mem_nhds (realFrozenChart_self_mem x)
  have hh : {v | v ∈ realFrozenChartDomain x ∧
      ‖realFrozenTransport g x (realFrozenChartInv x v)‖ < C ∧
      ‖realFrozenTransportBack g x (realFrozenChartInv x v)‖ < C} ∈ 𝓝 (realFrozenChart x x) := by
    filter_upwards [ho, hn] with v hv hnorm
    exact ⟨hv, hnorm.2, hnorm.1⟩
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp hh
  exact ⟨ρ, hρ, fun v hv => (hsub hv).1, fun v hv => (hsub hv).2⟩


theorem exists_realFrozenChart_distance_bound (g : SmoothMetric M) (x : M.Carrier)
    {C : ℝ} (hC : 1 < C) :
    letI := manifold_realSmooth M
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    ∃ ρ > (0 : ℝ), ∀ v ∈ Metric.ball (realFrozenChart x x) ρ,
      ∀ w ∈ Metric.ball (realFrozenChart x x) ρ,
        inducedDistance g.form (realFrozenChartInv x v) (realFrozenChartInv x w) ≤
          C * dist v w := by
  letI := manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  obtain ⟨ρ, hρ, hdom, hnorm⟩ := exists_realFrozenChart_ball_of_one_lt g x hC
  refine ⟨ρ, hρ, ?_⟩
  apply inducedDistance_le_of_chart_deriv g (realFrozenChartInv x) Metric.isOpen_ball
    (convex_ball _ _) (le_trans zero_le_one hC.le)
  · intro z hz
    exact (realFrozenChartInv_contMDiffAt g x z (hdom hz)).contMDiffWithinAt.of_le (by simp)
  · intro z hz u
    rw [realFrozenChartInv_mfderiv g x z u (hdom hz)]
    exact ((realFrozenTransport g x (realFrozenChartInv x z)).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right (hnorm z hz).1.le (norm_nonneg u))

set_option backward.isDefEq.respectTransparency false in
theorem realFrozenChart_exponential_radial_hasDerivAt_zero
    (g : SmoothMetric M) (x : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    letI := underlyingRealTangentInnerProductSpace g.form x
    HasDerivAt (fun t : ℝ => realFrozenChart x (realExponentialMap g x (t • v))) v 0 := by
  letI := manifold_realSmooth M
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  let e := (trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x).symmL ℝ x
  let w : ComplexVector n := realTangentCoords x x v
  have hv : realFrameCLM x x w = v :=
    realFrameCLM_realTangentCoords x x (mem_chart_source _ _) v
  have he : e w = v := by
    change realFrameCLM x x w = v
    exact hv
  have hd := e.hasFDerivAt.comp_hasDerivAt 0
    (realExponentialCoordinates_radial_hasDerivAt_zero g x w)
  rw [he] at hd
  convert hd using 1
  funext t
  simp only [realExponentialCoordinates, map_smul, hv]
  rfl


set_option backward.isDefEq.respectTransparency false in
/-- A minimizing broken radial geodesic has the same velocity on both sides
of its joining point. -/
theorem realExponential_no_corner (g : SmoothMetric M) (b : M.Carrier)
    (u v : TangentSpace 𝓘(ℝ, ComplexVector n) b) :
    letI := underlyingRealTangentNormedAddCommGroup g.form b
    letI := underlyingRealTangentInnerProductSpace g.form b
    ‖u‖ = 1 → ‖v‖ = 1 →
    (∀ᶠ h : ℝ in 𝓝[>] 0,
      inducedDistance g.form (realExponentialMap g b ((-h) • u))
        (realExponentialMap g b (h • v)) = 2 * h) → u = v := by
  letI := manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  letI := underlyingRealTangentNormedAddCommGroup g.form b
  letI := underlyingRealTangentInnerProductSpace g.form b
  intro hu hv hdist
  let a : ℝ → M.Carrier := fun h => realExponentialMap g b (h • (-u))
  let c : ℝ → M.Carrier := fun h => realExponentialMap g b (h • v)
  let A : ℝ → TangentSpace 𝓘(ℝ, ComplexVector n) b := realFrozenChart b ∘ a
  let B : ℝ → TangentSpace 𝓘(ℝ, ComplexVector n) b := realFrozenChart b ∘ c
  let F : ℝ → TangentSpace 𝓘(ℝ, ComplexVector n) b := fun h => B h - A h
  have ha0 : a 0 = b := by simp [a, realExponentialMap_zero]
  have hc0 : c 0 = b := by simp [c, realExponentialMap_zero]
  have hA : HasDerivAt A (-u) 0 :=
    realFrozenChart_exponential_radial_hasDerivAt_zero g b (-u)
  have hB : HasDerivAt B v 0 :=
    realFrozenChart_exponential_radial_hasDerivAt_zero g b v
  have hF : HasDerivAt F (v + u) 0 := by
    convert! hB.sub hA using 1
    simp only [sub_neg_eq_add]
  have hF0 : F 0 = 0 := by simp only [F, A, B, Function.comp_apply, ha0, hc0, sub_self]
  have hlim : Tendsto (fun h : ℝ => h⁻¹ • F h) (𝓝[>] 0) (𝓝 (v + u)) := by
    simpa only [zero_add, hF0, sub_zero] using hF.tendsto_slope_zero_right
  have hlower : ∀ C : ℝ, 1 < C → 2 ≤ C * ‖v + u‖ := by
    intro C hC
    obtain ⟨ρ, hρ, hbound⟩ := exists_realFrozenChart_distance_bound g b hC
    have hAball : ∀ᶠ h : ℝ in 𝓝 0, A h ∈ Metric.ball (realFrozenChart b b) ρ := by
      have h := hA.continuousAt.eventually (Metric.ball_mem_nhds (A 0) hρ)
      simpa only [A, Function.comp_apply, ha0, Metric.mem_ball] using h
    have hBball : ∀ᶠ h : ℝ in 𝓝 0, B h ∈ Metric.ball (realFrozenChart b b) ρ := by
      have h := hB.continuousAt.eventually (Metric.ball_mem_nhds (B 0) hρ)
      simpa only [B, Function.comp_apply, hc0, Metric.mem_ball] using h
    have haSource : ∀ᶠ h : ℝ in 𝓝 0,
        a h ∈ (extChartAt (ComplexModel n) b).source := by
      have hcont : ContinuousAt a 0 :=
        (realExponentialMap_radial_contMDiff g b (-u)).continuous.continuousAt
      have hn : (extChartAt (ComplexModel n) b).source ∈ 𝓝 (a 0) := by
        rw [ha0]
        exact extChartAt_source_mem_nhds (I := ComplexModel n) b
      exact hcont.eventually hn
    have hcSource : ∀ᶠ h : ℝ in 𝓝 0,
        c h ∈ (extChartAt (ComplexModel n) b).source := by
      have hcont : ContinuousAt c 0 :=
        (realExponentialMap_radial_contMDiff g b v).continuous.continuousAt
      have hn : (extChartAt (ComplexModel n) b).source ∈ 𝓝 (c 0) := by
        rw [hc0]
        exact extChartAt_source_mem_nhds (I := ComplexModel n) b
      exact hcont.eventually hn
    have hevent : ∀ᶠ h : ℝ in 𝓝[>] 0, 2 ≤ C * ‖h⁻¹ • F h‖ := by
      filter_upwards [hAball.filter_mono nhdsWithin_le_nhds,
        hBball.filter_mono nhdsWithin_le_nhds,
        haSource.filter_mono nhdsWithin_le_nhds,
        hcSource.filter_mono nhdsWithin_le_nhds,
        hdist, self_mem_nhdsWithin] with h hAh hBh hah hch hd hh
      have hhpos : 0 < h := hh
      have hd' : inducedDistance g.form (a h) (c h) = 2 * h := by
        simpa only [a, c, smul_neg, neg_smul] using hd
      have hb := hbound (A h) hAh (B h) hBh
      dsimp only [A, B, Function.comp_apply] at hb
      rw [realFrozenChartInv_realFrozenChart b (a h) hah,
        realFrozenChartInv_realFrozenChart b (c h) hch, hd'] at hb
      change 2 * h ≤ C * dist (A h) (B h) at hb
      have hn : dist (A h) (B h) = ‖F h‖ := by
        rw [dist_eq_norm, norm_sub_rev]
      rw [hn] at hb
      calc
        2 = (2 * h) / h := by field_simp
        _ ≤ (C * ‖F h‖) / h := (div_le_div_iff_of_pos_right hhpos).2 hb
        _ = C * ‖h⁻¹ • F h‖ := by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hhpos.le)]
          ring
    exact ge_of_tendsto (tendsto_const_nhds.mul hlim.norm) hevent
  have htwo : 2 ≤ ‖v + u‖ := by
    by_contra h
    have hlt : ‖v + u‖ < 2 := lt_of_not_ge h
    let C : ℝ := 1 + (2 - ‖v + u‖) / (2 * (‖v + u‖ + 1))
    have hp : 0 < 2 * (‖v + u‖ + 1) := by positivity
    have hC : 1 < C := by dsimp [C]; exact lt_add_of_pos_right _ (div_pos (by linarith) hp)
    have hb := hlower C hC
    have he : (C - 1) * (2 * (‖v + u‖ + 1)) = 2 - ‖v + u‖ := by
      dsimp [C]
      field_simp
      ring
    nlinarith [norm_nonneg (v + u)]
  have heq : ‖u + v‖ = ‖u‖ + ‖v‖ := by
    rw [hu, hv]
    have hb := norm_add_le u v
    rw [hu, hv] at hb
    rw [add_comm] at htwo
    linarith
  have he := norm_add_eq_iff_real.mp heq
  simpa only [hu, hv, one_smul] using he

end Yau.LeafProofs.L12Aux

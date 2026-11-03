import Yau.LeafProofs.L12ODEVariation
import Yau.LeafProofs.L12Exponential

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

set_option backward.isDefEq.respectTransparency false in
/-- A genuine coordinate spray solution lifts to an integral curve of the
actual global tangent-bundle spray. -/
theorem chartGeodesic_phase_isMIntegralCurveOn (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (η : ℝ → ComplexVector n × ComplexVector n) {s : Set ℝ}
    (hη : ∀ t ∈ s, (η t).1 ∈ chartTarget p.proj ∧
      HasDerivAt η (chartGeodesicSpray g.form p.proj (η t)) t) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    IsMIntegralCurveOn ((extChartAt (realPhaseModel n) p).symm ∘ η) (realGeodesicSpray g) s := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := realPhaseModel_boundaryless n
  intro t ht
  let xt := (extChartAt (realPhaseModel n) p).symm (η t)
  have htarg : η t ∈ (extChartAt (realPhaseModel n) p).target :=
    (realPhaseChart_target p (η t)).mpr (hη t ht).1
  have hft1 : xt ∈ (extChartAt (realPhaseModel n) p).source :=
    (extChartAt (realPhaseModel n) p).map_target htarg
  have hft2 : xt ∈ (extChartAt (realPhaseModel n) xt).source := mem_extChartAt_source _
  have hcoord : tangentCoordChange (realPhaseModel n) xt p xt (realGeodesicSpray g xt) =
      chartGeodesicSpray g.form p.proj (η t) := by
    simpa only [xt, (extChartAt (realPhaseModel n) p).right_inv htarg] using
      tangentCoordChange_realGeodesicSpray g p xt hft1
  have h : HasDerivAt η
      (tangentCoordChange (realPhaseModel n) xt p xt (realGeodesicSpray g xt)) t := by
    rw [hcoord]
    exact (hη t ht).2
  apply HasMFDerivAt.hasMFDerivWithinAt
  refine ⟨(continuousAt_extChartAt_symm'' htarg).comp h.continuousAt,
    HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  simp only [mfld_simps, hasDerivWithinAt_univ]
  change HasDerivAt ((extChartAt (realPhaseModel n) xt ∘
    (extChartAt (realPhaseModel n) p).symm) ∘ η) (realGeodesicSpray g xt) t
  rw [← tangentCoordChange_self (I := realPhaseModel n) (x := xt) (z := xt)
      (v := realGeodesicSpray g xt) hft2,
    ← tangentCoordChange_comp (x := p) ⟨⟨hft2, hft1⟩, hft2⟩]
  apply HasFDerivAt.comp_hasDerivAt _ _ h
  apply HasFDerivWithinAt.hasFDerivAt (s := Set.range (realPhaseModel n)) _
    (by rw [ModelWithCorners.range_eq_univ]; exact Filter.univ_mem)
  rw [← (extChartAt (realPhaseModel n) p).right_inv htarg]
  exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩

/-- A C1 family of genuine geodesics and its actual first variation, with
agreement with the already constructed unique global flow. -/
theorem exists_C1_chart_geodesic_variation (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ),
      ∃ φ : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n × ComplexVector n,
      ∃ V : (ComplexVector n × ComplexVector n) → ℝ →
        (ComplexVector n × ComplexVector n) →L[ℝ] (ComplexVector n × ComplexVector n),
      ContDiffOn ℝ 1 (Function.uncurry φ)
        (Metric.ball (extChartAt (realPhaseModel n) p p) r ×ˢ Set.Ioo (-ε) ε) ∧
      ContinuousOn (Function.uncurry V)
        (Metric.ball (extChartAt (realPhaseModel n) p p) r ×ˢ Set.Ioo (-ε) ε) ∧
      (∀ z ∈ Metric.ball (extChartAt (realPhaseModel n) p p) r,
        φ z 0 = z ∧ V z 0 = ContinuousLinearMap.id ℝ (ComplexVector n × ComplexVector n)) ∧
      (∀ z ∈ Metric.ball (extChartAt (realPhaseModel n) p p) r, ∀ t ∈ Set.Ioo (-ε) ε,
        φ z t ∈ (extChartAt (realPhaseModel n) p).target ∧
        (extChartAt (realPhaseModel n) p).symm (φ z t) =
          realGeodesicFlow g ((extChartAt (realPhaseModel n) p).symm z) t ∧
        HasDerivAt (φ z) (chartGeodesicSpray g.form p.proj (φ z t)) t ∧
        HasDerivAt (V z)
          ((fderiv ℝ (chartGeodesicSpray g.form p.proj) (φ z t)).comp (V z t)) t) ∧
      (∀ q ∈ Metric.ball (extChartAt (realPhaseModel n) p p) r ×ˢ Set.Ioo (-ε) ε,
        HasFDerivAt (fun z => φ z q.2) (V q.1 q.2) q.1) ∧
      Metric.ball (extChartAt (realPhaseModel n) p p) r ⊆
        (extChartAt (realPhaseModel n) p).target := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := realPhase_t2Space M
  letI := realPhaseModel_boundaryless n
  have hz₀ : extChartAt (realPhaseModel n) p p ∈
      chartTarget p.proj ×ˢ (Set.univ : Set (ComplexVector n)) :=
    ⟨(realPhaseChart_target p _).mp (mem_extChartAt_target p), Set.mem_univ _⟩
  have hO : IsOpen (chartTarget p.proj ×ˢ (Set.univ : Set (ComplexVector n))) :=
    (isOpen_extChartAt_target (I := ComplexModel n) p.proj).prod isOpen_univ
  have hF : ContDiffAt ℝ 2 (chartGeodesicSpray g.form p.proj)
      (extChartAt (realPhaseModel n) p p) :=
    ((chartGeodesicSpray_contDiffOn g p.proj).contDiffAt (hO.mem_nhds hz₀)).of_le (by simp)
  obtain ⟨r, hr, ε, hε, φ, V, hφc, hVc, hinit, hsol, hspace, _⟩ :=
    exists_C1_local_ODE_flow hF (isOpen_extChartAt_target (I := realPhaseModel n) p)
      (mem_extChartAt_target p)
  have h0 : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hG := (realGeodesicSpray_contMDiff g).of_le
    (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)
  refine ⟨r, hr, ε, hε, φ, V, hφc, hVc, hinit, ?_, hspace, ?_⟩
  · intro z hz
    have hη : ∀ t ∈ Set.Ioo (-ε) ε, (φ z t).1 ∈ chartTarget p.proj ∧
        HasDerivAt (φ z) (chartGeodesicSpray g.form p.proj (φ z t)) t := by
      intro t ht
      exact ⟨(realPhaseChart_target p _).mp (hsol z hz t ht).1, (hsol z hz t ht).2.1⟩
    have hγ := chartGeodesic_phase_isMIntegralCurveOn g p (φ z) hη
    have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless h0 hG hγ
      ((realGeodesicFlow_integral g ((extChartAt (realPhaseModel n) p).symm z)).isMIntegralCurveOn _)
      (by rw [Function.comp_apply, (hinit z hz).1, realGeodesicFlow_zero])
    intro t ht
    exact ⟨(hsol z hz t ht).1, heq ht, (hsol z hz t ht).2⟩
  · intro z hz
    have h := (hsol z hz 0 h0).1
    rwa [(hinit z hz).1] at h

/-- The actual global geodesic flow, expressed in one fixed phase chart. -/
def realGeodesicChartFlow (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (z : ComplexVector n × ComplexVector n) (t : ℝ) :
    ComplexVector n × ComplexVector n := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  exact extChartAt (realPhaseModel n) p
    (realGeodesicFlow g ((extChartAt (realPhaseModel n) p).symm z) t)

/-- Local C1 initial-state dependence and the variational equation for the
actual chosen global geodesic flow in fixed coordinates. -/
theorem realGeodesicChartFlow_local_C1 (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ),
      ∃ V : (ComplexVector n × ComplexVector n) → ℝ →
        (ComplexVector n × ComplexVector n) →L[ℝ] (ComplexVector n × ComplexVector n),
      ContDiffOn ℝ 1 (Function.uncurry (realGeodesicChartFlow g p))
        (Metric.ball (extChartAt (realPhaseModel n) p p) r ×ˢ Set.Ioo (-ε) ε) ∧
      ContinuousOn (Function.uncurry V)
        (Metric.ball (extChartAt (realPhaseModel n) p p) r ×ˢ Set.Ioo (-ε) ε) ∧
      (∀ z ∈ Metric.ball (extChartAt (realPhaseModel n) p p) r,
        V z 0 = ContinuousLinearMap.id ℝ (ComplexVector n × ComplexVector n)) ∧
      (∀ z ∈ Metric.ball (extChartAt (realPhaseModel n) p p) r, ∀ t ∈ Set.Ioo (-ε) ε,
        realGeodesicFlow g ((extChartAt (realPhaseModel n) p).symm z) t ∈
          (extChartAt (realPhaseModel n) p).source ∧
        HasDerivAt (realGeodesicChartFlow g p z)
          (chartGeodesicSpray g.form p.proj (realGeodesicChartFlow g p z t)) t ∧
        HasDerivAt (V z)
          ((fderiv ℝ (chartGeodesicSpray g.form p.proj)
            (realGeodesicChartFlow g p z t)).comp (V z t)) t ∧
        HasFDerivAt (fun z' => realGeodesicChartFlow g p z' t) (V z t) z) ∧
      Metric.ball (extChartAt (realPhaseModel n) p p) r ⊆
        (extChartAt (realPhaseModel n) p).target := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  obtain ⟨r, hr, ε, hε, φ, V, hφc, hVc, hinit, hsol, hspace, hball⟩ :=
    exists_C1_chart_geodesic_variation g p
  have heq : ∀ z ∈ Metric.ball (extChartAt (realPhaseModel n) p p) r,
      ∀ t ∈ Set.Ioo (-ε) ε, realGeodesicChartFlow g p z t = φ z t := by
    intro z hz t ht
    unfold realGeodesicChartFlow
    rw [← (hsol z hz t ht).2.1]
    exact (extChartAt (realPhaseModel n) p).right_inv (hsol z hz t ht).1
  have hc : ContDiffOn ℝ 1 (Function.uncurry (realGeodesicChartFlow g p))
      (Metric.ball (extChartAt (realPhaseModel n) p p) r ×ˢ Set.Ioo (-ε) ε) :=
    (contDiffOn_congr (fun q hq => heq q.1 hq.1 q.2 hq.2)).mpr hφc
  refine ⟨r, hr, ε, hε, V, hc, hVc, fun z hz => (hinit z hz).2, ?_, hball⟩
  intro z hz t ht
  have hEt : realGeodesicChartFlow g p z =ᶠ[𝓝 t] φ z := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact heq z hz u hu
  have hEz : (fun z' => realGeodesicChartFlow g p z' t) =ᶠ[𝓝 z] (fun z' => φ z' t) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with z' hz'
    exact heq z' hz' t ht
  have htime := (hEt.hasDerivAt_iff).mpr (hsol z hz t ht).2.2.1
  have hvar := (hsol z hz t ht).2.2.2
  rw [← heq z hz t ht] at htime hvar
  refine ⟨?_, htime, hvar, hEz.hasFDerivAt_iff.mpr (hspace (z, t) ⟨hz, ht⟩)⟩
  rw [← (hsol z hz t ht).2.1]
  exact (extChartAt (realPhaseModel n) p).map_target (hsol z hz t ht).1

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- The genuine phase-space geodesic flow is jointly C1 on a neighborhood
of each initial state and zero time. -/
theorem realGeodesicFlow_local_contMDiff (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ∃ U : Set (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier), IsOpen U ∧ p ∈ U ∧
      ∃ ε > (0 : ℝ), ContMDiffOn ((realPhaseModel n).prod 𝓘(ℝ, ℝ))
        (realPhaseModel n) 1
        (fun q : (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) × ℝ =>
          realGeodesicFlow g q.1 q.2)
        (U ×ˢ Set.Ioo (-ε) ε) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := realPhaseModel_boundaryless n
  obtain ⟨r, hr, ε, hε, V, hC, hV, hinit, hsol, hball⟩ :=
    realGeodesicChartFlow_local_C1 g p
  let e := extChartAt (realPhaseModel n) p
  let U := e.source ∩ e ⁻¹' Metric.ball (e p) r
  have hU : IsOpen U :=
    (continuousOn_extChartAt p).isOpen_inter_preimage (isOpen_extChartAt_source p)
      Metric.isOpen_ball
  have hpU : p ∈ U := ⟨mem_extChartAt_source p, Metric.mem_ball_self hr⟩
  have hQ : IsOpen (Metric.ball (e p) r ×ˢ Set.Ioo (-ε) ε) :=
    Metric.isOpen_ball.prod isOpen_Ioo
  have hR : IsOpen (U ×ˢ Set.Ioo (-ε) ε) := hU.prod isOpen_Ioo
  refine ⟨U, hU, hpU, ε, hε, ?_⟩
  intro q hq
  have hchart : ContMDiffAt (realPhaseModel n) 𝓘(ℝ, ComplexVector n × ComplexVector n)
      1 e q.1 :=
    contMDiffAt_extChartAt' (by simpa only [e, extChartAt_source] using hq.1.1)
  have hin : ContMDiffAt ((realPhaseModel n).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, (ComplexVector n × ComplexVector n) × ℝ) 1
      (fun a : (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) × ℝ =>
        (e a.1, a.2)) q :=
    (hchart.comp q contMDiffAt_fst).prodMk_space contMDiffAt_snd
  have hcoords' : ContDiffAt ℝ 1
      (Function.uncurry (realGeodesicChartFlow g p)) (e q.1, q.2) := by
    apply hC.contDiffAt
    exact hQ.mem_nhds ⟨hq.1.2, hq.2⟩
  have hcoords : ContMDiffAt 𝓘(ℝ, (ComplexVector n × ComplexVector n) × ℝ)
      𝓘(ℝ, ComplexVector n × ComplexVector n) 1
      (Function.uncurry (realGeodesicChartFlow g p)) (e q.1, q.2) :=
    contMDiffAt_iff_contDiffAt.mpr hcoords'
  have hs : realGeodesicFlow g (e.symm (e q.1)) q.2 ∈ e.source :=
    (hsol (e q.1) hq.1.2 q.2 hq.2).1
  have htarget : realGeodesicChartFlow g p (e q.1) q.2 ∈ e.target := e.map_source hs
  have hsymm : ContMDiffAt 𝓘(ℝ, ComplexVector n × ComplexVector n)
      (realPhaseModel n) 1 e.symm (realGeodesicChartFlow g p (e q.1) q.2) :=
    (contMDiffOn_extChartAt_symm p).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds htarget)
  have hcomp := hsymm.comp q (hcoords.comp q hin)
  have hevent : (fun a => e.symm (realGeodesicChartFlow g p (e a.1) a.2)) =ᶠ[𝓝 q]
      (fun a => realGeodesicFlow g a.1 a.2) := by
    filter_upwards [hR.mem_nhds hq] with a ha
    have hs' := (hsol (e a.1) ha.1.2 a.2 ha.2).1
    change e.symm (e (realGeodesicFlow g (e.symm (e a.1)) a.2)) = _
    rw [e.left_inv hs', e.left_inv ha.1.1]
  exact (hevent.contMDiffAt_iff.mp hcomp).contMDiffWithinAt

/-- Compact sets of genuine initial states admit a common time interval on
which the joint actual geodesic flow is C1 at every point. -/
theorem realGeodesicFlow_uniform_local_contMDiff (g : SmoothMetric M)
    {K : Set (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)}
    (hK : letI := manifold_realSmooth M; IsCompact K) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ∃ ε > (0 : ℝ), ∀ p ∈ K, ∀ t ∈ Set.Ioo (-ε) ε,
      ContMDiffAt ((realPhaseModel n).prod 𝓘(ℝ, ℝ)) (realPhaseModel n) 1
        (fun q : (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) × ℝ =>
          realGeodesicFlow g q.1 q.2) (p, t) := by
  classical
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  choose U hU hpU ε hε hreg using realGeodesicFlow_local_contMDiff g
  let N := ⋃ p, U p ×ˢ Set.Ioo (-ε p) (ε p)
  have hN : IsOpen N := isOpen_iUnion fun p => (hU p).prod isOpen_Ioo
  have hKN : K ×ˢ ({0} : Set ℝ) ⊆ N := by
    intro q hq
    have hq0 : q.2 = 0 := hq.2
    exact Set.mem_iUnion.mpr ⟨q.1, hpU q.1, by rw [hq0]; exact ⟨by linarith [hε q.1], hε q.1⟩⟩
  obtain ⟨u, v, hu, hv, hKu, h0v, huv⟩ :=
    generalized_tube_lemma hK isCompact_singleton hN hKN
  have h0v' : (0 : ℝ) ∈ v := h0v (by simp)
  obtain ⟨δ, hδ, hδv⟩ := Metric.mem_nhds_iff.mp (hv.mem_nhds h0v')
  refine ⟨δ, hδ, ?_⟩
  intro p hp t ht
  have htv : t ∈ v := hδv (by simpa [Metric.mem_ball, Real.dist_eq, sub_zero] using abs_lt.mpr ht)
  have hptN : (p, t) ∈ N := huv ⟨hKu hp, htv⟩
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hptN
  exact (hreg a).contMDiffAt (((hU a).prod isOpen_Ioo).mem_nhds ha)

set_option backward.isDefEq.respectTransparency false in
/-- The actual time-t geodesic flow has C1 dependence on every initial
state, obtained by finitely many local flow compositions. -/
theorem realGeodesicFlow_initial_contMDiffAt (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiffAt (realPhaseModel n) (realPhaseModel n) 1
      (fun q => realGeodesicFlow g q t) p := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  let K := realGeodesicFlow g p '' Set.Icc (-|t|) |t|
  have hK : IsCompact K :=
    isCompact_Icc.image (realGeodesicFlow_contMDiff g p).continuous
  obtain ⟨ε, hε, hreg⟩ := realGeodesicFlow_uniform_local_contMDiff g hK
  obtain ⟨N, hN⟩ := exists_nat_gt (|t| / ε)
  let d := t / (N + 1 : ℝ)
  have hden : (0 : ℝ) < N + 1 := by positivity
  have hd : |d| < ε := by
    dsimp [d]
    rw [abs_div, abs_of_pos hden]
    apply (div_lt_iff₀ hden).mpr
    have h := (div_lt_iff₀ hε).mp hN
    nlinarith
  have hstep : ∀ k : ℕ, k ≤ N + 1 → |(k : ℝ) * d| ≤ |t| := by
    intro k hk
    have hk' : (k : ℝ) ≤ N + 1 := by exact_mod_cast hk
    dsimp [d]
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k), abs_div, abs_of_pos hden]
    have hmul := mul_le_mul_of_nonneg_right hk' (abs_nonneg t)
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hden).mpr (by nlinarith)
  have hiter : ∀ k : ℕ, k ≤ N + 1 →
      ContMDiffAt (realPhaseModel n) (realPhaseModel n) 1
        (fun q => realGeodesicFlow g q ((k : ℝ) * d)) p := by
    intro k
    induction k with
    | zero =>
        intro hk
        have hfun : (fun q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier =>
            realGeodesicFlow g q ((0 : ℕ) * d)) = id := by
          funext q
          simp only [Nat.cast_zero, zero_mul, realGeodesicFlow_zero, id_eq]
        rw [hfun]
        exact contMDiffAt_id
    | succ k ih =>
        intro hk
        have hk' : k ≤ N + 1 := Nat.le_trans (Nat.le_succ k) hk
        have hpk : realGeodesicFlow g p ((k : ℝ) * d) ∈ K :=
          ⟨(k : ℝ) * d, abs_le.mp (hstep k hk'), rfl⟩
        have hsmall := hreg _ hpk d (abs_lt.mp hd)
        have hc := hsmall.comp p ((ih hk').prodMk contMDiffAt_const)
        convert hc using 1
        funext q
        simp only [Function.comp_apply, realGeodesicFlow_add, Nat.cast_add, Nat.cast_one,
          add_mul, one_mul]
  have htime : ((N + 1 : ℕ) : ℝ) * d = t := by
    push_cast
    dsimp [d]
    field_simp
  simpa only [htime] using hiter (N + 1) le_rfl

set_option backward.isDefEq.respectTransparency false in
/-- Global joint C1 dependence of the genuine complete geodesic flow. -/
theorem realGeodesicFlow_joint_contMDiff (g : SmoothMetric M) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiff ((realPhaseModel n).prod 𝓘(ℝ, ℝ)) (realPhaseModel n) 1
      (fun q : (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) × ℝ =>
        realGeodesicFlow g q.1 q.2) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  intro q
  obtain ⟨U, hU, hpU, ε, hε, hreg⟩ :=
    realGeodesicFlow_local_contMDiff g (realGeodesicFlow g q.1 q.2)
  have hz : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hlocal : ContMDiffAt ((realPhaseModel n).prod 𝓘(ℝ, ℝ)) (realPhaseModel n) 1
      (fun a : (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) × ℝ =>
        realGeodesicFlow g a.1 a.2) (realGeodesicFlow g q.1 q.2, 0) :=
    hreg.contMDiffAt ((hU.prod isOpen_Ioo).mem_nhds ⟨hpU, hz⟩)
  have hfirst : ContMDiffAt ((realPhaseModel n).prod 𝓘(ℝ, ℝ)) (realPhaseModel n) 1
      (fun a : (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) × ℝ =>
        realGeodesicFlow g a.1 q.2) q :=
    (realGeodesicFlow_initial_contMDiffAt g q.1 q.2).comp q contMDiffAt_fst
  have hsecond : ContMDiffAt ((realPhaseModel n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 1
      (fun a : (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) × ℝ => a.2 - q.2) q :=
    (contMDiffAt_snd (I := realPhaseModel n) (J := 𝓘(ℝ, ℝ))).sub contMDiffAt_const
  have hlocal' : ContMDiffAt ((realPhaseModel n).prod 𝓘(ℝ, ℝ)) (realPhaseModel n) 1
      (fun a : (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) × ℝ =>
        realGeodesicFlow g a.1 a.2) (realGeodesicFlow g q.1 q.2, q.2 - q.2) := by
    simpa only [sub_self] using hlocal
  have hcomp := hlocal'.comp q (hfirst.prodMk hsecond)
  convert hcomp using 1
  funext a
  simp only [Function.comp_apply, ← realGeodesicFlow_add, add_sub_cancel]

set_option backward.isDefEq.respectTransparency false in
/-- Inserting a genuine tangent vector in its fixed fiber is smooth. -/
theorem realTangentFiber_contMDiff (g : SmoothMetric M) (x : M.Carrier) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    letI := underlyingRealTangentInnerProductSpace g.form x
    ContMDiff 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) x) (realPhaseModel n) ∞
      (fun v : TangentSpace 𝓘(ℝ, ComplexVector n) x =>
        (⟨x, v⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  intro v
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨contMDiffAt_const, ?_⟩
  have heq : (fun w : TangentSpace 𝓘(ℝ, ComplexVector n) x =>
      (trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) x
        (⟨x, w⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)).2) =
      realTangentCoords x x := by
    funext w
    exact (Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _
      (mem_baseSet_trivializationAt (ComplexVector n)
        (TangentSpace 𝓘(ℝ, ComplexVector n)) x) w).symm
  rw [heq]
  exact (realTangentCoords x x).contMDiff.contMDiffAt

/-- The actual globally defined exponential depends C1 on its initial
position and velocity as a map from the genuine tangent bundle. -/
theorem realExponentialBundle_contMDiff (g : SmoothMetric M) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiff (realPhaseModel n) 𝓘(ℝ, ComplexVector n) 1
      (fun p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier =>
        (realGeodesicFlow g p 1).proj) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  have hflow := (realGeodesicFlow_joint_contMDiff g).comp
    (contMDiff_id.prodMk (contMDiff_const (c := (1 : ℝ))))
  exact (Bundle.contMDiff_proj (IB := 𝓘(ℝ, ComplexVector n)) (n := 1)
    (TangentSpace 𝓘(ℝ, ComplexVector n))).comp hflow

/-- C1 regularity of the genuine Riemannian exponential in every tangent
fiber, derived from the actual variational ODE. -/
theorem realExponentialMap_contMDiff (g : SmoothMetric M) (x : M.Carrier) :
    letI := manifold_realSmooth M
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    letI := underlyingRealTangentInnerProductSpace g.form x
    ContMDiff 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) x) 𝓘(ℝ, ComplexVector n) 1
      (realExponentialMap g x) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  exact (realExponentialBundle_contMDiff g).comp
    ((realTangentFiber_contMDiff g x).of_le (by simp))

end Yau.LeafProofs.L12Aux

import Yau.LeafProofs.L23FieldMetricLocalFlow
import Yau.LeafProofs.L12ParallelTransport

/-! Smooth dependence of the same genuine parallel transport flow. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem realParallelTransportFlow_add (g : SmoothMetric M)
    (p : realTransportBundle M) (s t : ℝ) :
    realParallelTransportFlow g p (s + t) =
      realParallelTransportFlow g (realParallelTransportFlow g p s) t := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  have h := realParallelTransportFlow_unique g (realParallelTransportFlow g p s)
    (realParallelTransportFlow g p ∘ (· + s)) (by simp)
    ((realParallelTransportFlow_integral g p).comp_add s)
  simpa only [Function.comp_apply, add_comm] using congrFun h t

set_option backward.isDefEq.respectTransparency false in
/-- A genuine coordinate spray solution lifts to an integral curve of the
actual global tangent-bundle spray. -/
theorem chartParallelTransport_phase_isMIntegralCurveOn (g : SmoothMetric M)
    (p : realTransportBundle M)
    (η : ℝ → ComplexVector n × (ComplexVector n × ComplexVector n)) {s : Set ℝ}
    (hη : ∀ t ∈ s, (η t).1 ∈ chartTarget p.proj ∧
      HasDerivAt η (chartParallelTransportField g.form p.proj (η t)) t) :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    IsMIntegralCurveOn ((extChartAt (realTransportModel n) p).symm ∘ η) (realParallelTransportSpray g) s := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  letI := realTransportModel_boundaryless n
  intro t ht
  let xt := (extChartAt (realTransportModel n) p).symm (η t)
  have htarg : η t ∈ (extChartAt (realTransportModel n) p).target :=
    (realTransportChart_target p (η t)).mpr (hη t ht).1
  have hft1 : xt ∈ (extChartAt (realTransportModel n) p).source :=
    (extChartAt (realTransportModel n) p).map_target htarg
  have hft2 : xt ∈ (extChartAt (realTransportModel n) xt).source := mem_extChartAt_source _
  have hcoord : tangentCoordChange (realTransportModel n) xt p xt (realParallelTransportSpray g xt) =
      chartParallelTransportField g.form p.proj (η t) := by
    simpa only [xt, (extChartAt (realTransportModel n) p).right_inv htarg] using
      tangentCoordChange_realParallelTransportSpray g p xt hft1
  have h : HasDerivAt η
      (tangentCoordChange (realTransportModel n) xt p xt (realParallelTransportSpray g xt)) t := by
    rw [hcoord]
    exact (hη t ht).2
  apply HasMFDerivAt.hasMFDerivWithinAt
  refine ⟨(continuousAt_extChartAt_symm'' htarg).comp h.continuousAt,
    HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  simp only [mfld_simps, hasDerivWithinAt_univ]
  change HasDerivAt ((extChartAt (realTransportModel n) xt ∘
    (extChartAt (realTransportModel n) p).symm) ∘ η) (realParallelTransportSpray g xt) t
  rw [← tangentCoordChange_self (I := realTransportModel n) (x := xt) (z := xt)
      (v := realParallelTransportSpray g xt) hft2,
    ← tangentCoordChange_comp (x := p) ⟨⟨hft2, hft1⟩, hft2⟩]
  apply HasFDerivAt.comp_hasDerivAt _ _ h
  apply HasFDerivWithinAt.hasFDerivAt (s := Set.range (realTransportModel n)) _
    (by rw [ModelWithCorners.range_eq_univ]; exact Filter.univ_mem)
  rw [← (extChartAt (realTransportModel n) p).right_inv htarg]
  exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩

def realParallelTransportChartFlow (g : SmoothMetric M)
    (p : realTransportBundle M)
    (z : ComplexVector n × (ComplexVector n × ComplexVector n)) (t : ℝ) :
    ComplexVector n × (ComplexVector n × ComplexVector n) := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  exact extChartAt (realTransportModel n) p
    (realParallelTransportFlow g ((extChartAt (realTransportModel n) p).symm z) t)

theorem exists_finiteOrder_chart_transport_variation_order (m : ℕ) (g : SmoothMetric M)
    (p : realTransportBundle M) :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ),
      ∃ φ : (ComplexVector n × (ComplexVector n × ComplexVector n)) → ℝ → ComplexVector n × (ComplexVector n × ComplexVector n),
      ∃ V : (ComplexVector n × (ComplexVector n × ComplexVector n)) → ℝ →
        (ComplexVector n × (ComplexVector n × ComplexVector n)) →L[ℝ] (ComplexVector n × (ComplexVector n × ComplexVector n)),
      ContDiffOn ℝ m (Function.uncurry φ)
        (Metric.ball (extChartAt (realTransportModel n) p p) r ×ˢ Set.Ioo (-ε) ε) ∧
      ContinuousOn (Function.uncurry V)
        (Metric.ball (extChartAt (realTransportModel n) p p) r ×ˢ Set.Ioo (-ε) ε) ∧
      (∀ z ∈ Metric.ball (extChartAt (realTransportModel n) p p) r,
        φ z 0 = z ∧ V z 0 = ContinuousLinearMap.id ℝ (ComplexVector n × (ComplexVector n × ComplexVector n))) ∧
      (∀ z ∈ Metric.ball (extChartAt (realTransportModel n) p p) r, ∀ t ∈ Set.Ioo (-ε) ε,
        φ z t ∈ (extChartAt (realTransportModel n) p).target ∧
        (extChartAt (realTransportModel n) p).symm (φ z t) =
          realParallelTransportFlow g ((extChartAt (realTransportModel n) p).symm z) t ∧
        HasDerivAt (φ z) (chartParallelTransportField g.form p.proj (φ z t)) t ∧
        HasDerivAt (V z)
          ((fderiv ℝ (chartParallelTransportField g.form p.proj) (φ z t)).comp (V z t)) t) ∧
      (∀ q ∈ Metric.ball (extChartAt (realTransportModel n) p p) r ×ˢ Set.Ioo (-ε) ε,
        HasFDerivAt (fun z => φ z q.2) (V q.1 q.2) q.1) ∧
      Metric.ball (extChartAt (realTransportModel n) p p) r ⊆
        (extChartAt (realTransportModel n) p).target := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  letI := realTransport_t2Space M
  letI := realTransportModel_boundaryless n
  have hz₀ : extChartAt (realTransportModel n) p p ∈
      chartTarget p.proj ×ˢ (Set.univ : Set (ComplexVector n × ComplexVector n)) :=
    ⟨(realTransportChart_target p _).mp (mem_extChartAt_target p), Set.mem_univ _⟩
  have hO : IsOpen (chartTarget p.proj ×ˢ (Set.univ : Set (ComplexVector n × ComplexVector n))) :=
    (isOpen_extChartAt_target (I := ComplexModel n) p.proj).prod isOpen_univ
  have hF : ContDiffOn ℝ ∞ (chartParallelTransportField g.form p.proj)
      (extChartAt (realTransportModel n) p).target := by
    apply (chartParallelTransportField_contDiffOn g p.proj).mono
    intro z hz
    exact ⟨(realTransportChart_target p z).mp hz, Set.mem_univ _⟩
  obtain ⟨r, hr, ε, hε, φ, V, hφc, hVc, hinit, hsol, hspace, _⟩ :=
    L23Aux.localODEFlowOrder m (ComplexVector n × (ComplexVector n × ComplexVector n))
      (chartParallelTransportField g.form p.proj) (extChartAt (realTransportModel n) p).target
      (extChartAt (realTransportModel n) p p) hF
      (isOpen_extChartAt_target (I := realTransportModel n) p) (mem_extChartAt_target p)
  have h0 : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hG := (realParallelTransportSpray_contMDiff g).of_le
    (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)
  refine ⟨r, hr, ε, hε, φ, V, hφc, hVc, hinit, ?_, hspace, ?_⟩
  · intro z hz
    have hη : ∀ t ∈ Set.Ioo (-ε) ε, (φ z t).1 ∈ chartTarget p.proj ∧
        HasDerivAt (φ z) (chartParallelTransportField g.form p.proj (φ z t)) t := by
      intro t ht
      exact ⟨(realTransportChart_target p _).mp (hsol z hz t ht).1, (hsol z hz t ht).2.1⟩
    have hγ := chartParallelTransport_phase_isMIntegralCurveOn g p (φ z) hη
    have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless h0 hG hγ
      ((realParallelTransportFlow_integral g ((extChartAt (realTransportModel n) p).symm z)).isMIntegralCurveOn _)
      (by rw [Function.comp_apply, (hinit z hz).1, realParallelTransportFlow_zero])
    intro t ht
    exact ⟨(hsol z hz t ht).1, heq ht, (hsol z hz t ht).2⟩
  · intro z hz
    have h := (hsol z hz 0 h0).1
    rwa [(hinit z hz).1] at h

theorem realParallelTransportChartFlow_local_finiteOrder_order (m : ℕ) (g : SmoothMetric M)
    (p : realTransportBundle M) :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ),
      ∃ V : (ComplexVector n × (ComplexVector n × ComplexVector n)) → ℝ →
        (ComplexVector n × (ComplexVector n × ComplexVector n)) →L[ℝ] (ComplexVector n × (ComplexVector n × ComplexVector n)),
      ContDiffOn ℝ m (Function.uncurry (realParallelTransportChartFlow g p))
        (Metric.ball (extChartAt (realTransportModel n) p p) r ×ˢ Set.Ioo (-ε) ε) ∧
      ContinuousOn (Function.uncurry V)
        (Metric.ball (extChartAt (realTransportModel n) p p) r ×ˢ Set.Ioo (-ε) ε) ∧
      (∀ z ∈ Metric.ball (extChartAt (realTransportModel n) p p) r,
        V z 0 = ContinuousLinearMap.id ℝ (ComplexVector n × (ComplexVector n × ComplexVector n))) ∧
      (∀ z ∈ Metric.ball (extChartAt (realTransportModel n) p p) r, ∀ t ∈ Set.Ioo (-ε) ε,
        realParallelTransportFlow g ((extChartAt (realTransportModel n) p).symm z) t ∈
          (extChartAt (realTransportModel n) p).source ∧
        HasDerivAt (realParallelTransportChartFlow g p z)
          (chartParallelTransportField g.form p.proj (realParallelTransportChartFlow g p z t)) t ∧
        HasDerivAt (V z)
          ((fderiv ℝ (chartParallelTransportField g.form p.proj)
            (realParallelTransportChartFlow g p z t)).comp (V z t)) t ∧
        HasFDerivAt (fun z' => realParallelTransportChartFlow g p z' t) (V z t) z) ∧
      Metric.ball (extChartAt (realTransportModel n) p p) r ⊆
        (extChartAt (realTransportModel n) p).target := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  obtain ⟨r, hr, ε, hε, φ, V, hφc, hVc, hinit, hsol, hspace, hball⟩ :=
    exists_finiteOrder_chart_transport_variation_order m g p
  have heq : ∀ z ∈ Metric.ball (extChartAt (realTransportModel n) p p) r,
      ∀ t ∈ Set.Ioo (-ε) ε, realParallelTransportChartFlow g p z t = φ z t := by
    intro z hz t ht
    unfold realParallelTransportChartFlow
    rw [← (hsol z hz t ht).2.1]
    exact (extChartAt (realTransportModel n) p).right_inv (hsol z hz t ht).1
  have hc : ContDiffOn ℝ m (Function.uncurry (realParallelTransportChartFlow g p))
      (Metric.ball (extChartAt (realTransportModel n) p p) r ×ˢ Set.Ioo (-ε) ε) :=
    (contDiffOn_congr (fun q hq => heq q.1 hq.1 q.2 hq.2)).mpr hφc
  refine ⟨r, hr, ε, hε, V, hc, hVc, fun z hz => (hinit z hz).2, ?_, hball⟩
  intro z hz t ht
  have hEt : realParallelTransportChartFlow g p z =ᶠ[𝓝 t] φ z := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact heq z hz u hu
  have hEz : (fun z' => realParallelTransportChartFlow g p z' t) =ᶠ[𝓝 z] (fun z' => φ z' t) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with z' hz'
    exact heq z' hz' t ht
  have htime := (hEt.hasDerivAt_iff).mpr (hsol z hz t ht).2.2.1
  have hvar := (hsol z hz t ht).2.2.2
  rw [← heq z hz t ht] at htime hvar
  refine ⟨?_, htime, hvar, hEz.hasFDerivAt_iff.mpr (hspace (z, t) ⟨hz, ht⟩)⟩
  rw [← (hsol z hz t ht).2.1]
  exact (extChartAt (realTransportModel n) p).map_target (hsol z hz t ht).1

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- The genuine phase-space geodesic flow is jointly C1 on a neighborhood
of each initial state and zero time. -/
theorem realParallelTransportFlow_local_contMDiff_order (m : ℕ) (g : SmoothMetric M)
    (p : realTransportBundle M) :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    ∃ U : Set (realTransportBundle M), IsOpen U ∧ p ∈ U ∧
      ∃ ε > (0 : ℝ), ContMDiffOn ((realTransportModel n).prod 𝓘(ℝ, ℝ))
        (realTransportModel n) m
        (fun q : (realTransportBundle M) × ℝ =>
          realParallelTransportFlow g q.1 q.2)
        (U ×ˢ Set.Ioo (-ε) ε) := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  letI := realTransportModel_boundaryless n
  obtain ⟨r, hr, ε, hε, V, hC, hV, hinit, hsol, hball⟩ :=
    realParallelTransportChartFlow_local_finiteOrder_order m g p
  let e := extChartAt (realTransportModel n) p
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
  have hchart : ContMDiffAt (realTransportModel n) 𝓘(ℝ, ComplexVector n × (ComplexVector n × ComplexVector n))
      m e q.1 :=
    contMDiffAt_extChartAt' (by simpa only [e, extChartAt_source] using hq.1.1)
  have hin : ContMDiffAt ((realTransportModel n).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, (ComplexVector n × (ComplexVector n × ComplexVector n)) × ℝ) m
      (fun a : (realTransportBundle M) × ℝ =>
        (e a.1, a.2)) q :=
    (hchart.comp q contMDiffAt_fst).prodMk_space contMDiffAt_snd
  have hcoords' : ContDiffAt ℝ m
      (Function.uncurry (realParallelTransportChartFlow g p)) (e q.1, q.2) := by
    apply hC.contDiffAt
    exact hQ.mem_nhds ⟨hq.1.2, hq.2⟩
  have hcoords : ContMDiffAt 𝓘(ℝ, (ComplexVector n × (ComplexVector n × ComplexVector n)) × ℝ)
      𝓘(ℝ, ComplexVector n × (ComplexVector n × ComplexVector n)) m
      (Function.uncurry (realParallelTransportChartFlow g p)) (e q.1, q.2) :=
    contMDiffAt_iff_contDiffAt.mpr hcoords'
  have hs : realParallelTransportFlow g (e.symm (e q.1)) q.2 ∈ e.source :=
    (hsol (e q.1) hq.1.2 q.2 hq.2).1
  have htarget : realParallelTransportChartFlow g p (e q.1) q.2 ∈ e.target := e.map_source hs
  have hsymm : ContMDiffAt 𝓘(ℝ, ComplexVector n × (ComplexVector n × ComplexVector n))
      (realTransportModel n) m e.symm (realParallelTransportChartFlow g p (e q.1) q.2) :=
    (contMDiffOn_extChartAt_symm p).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds htarget)
  have hcomp := hsymm.comp q (hcoords.comp q hin)
  have hevent : (fun a => e.symm (realParallelTransportChartFlow g p (e a.1) a.2)) =ᶠ[𝓝 q]
      (fun a => realParallelTransportFlow g a.1 a.2) := by
    filter_upwards [hR.mem_nhds hq] with a ha
    have hs' := (hsol (e a.1) ha.1.2 a.2 ha.2).1
    change e.symm (e (realParallelTransportFlow g (e.symm (e a.1)) a.2)) = _
    rw [e.left_inv hs', e.left_inv ha.1.1]
  exact (hevent.contMDiffAt_iff.mp hcomp).contMDiffWithinAt

/-- Compact sets of genuine initial states admit a common time interval on
which the joint actual geodesic flow is C1 at every point. -/
theorem realParallelTransportFlow_uniform_local_contMDiff_order (m : ℕ) (g : SmoothMetric M)
    {K : Set (realTransportBundle M)}
    (hK : letI := manifold_realSmooth M; IsCompact K) :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    ∃ ε > (0 : ℝ), ∀ p ∈ K, ∀ t ∈ Set.Ioo (-ε) ε,
      ContMDiffAt ((realTransportModel n).prod 𝓘(ℝ, ℝ)) (realTransportModel n) m
        (fun q : (realTransportBundle M) × ℝ =>
          realParallelTransportFlow g q.1 q.2) (p, t) := by
  classical
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  choose U hU hpU ε hε hreg using realParallelTransportFlow_local_contMDiff_order m g
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
theorem realParallelTransportFlow_initial_contMDiffAt_order (m : ℕ) (g : SmoothMetric M)
    (p : realTransportBundle M) (t : ℝ) :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    ContMDiffAt (realTransportModel n) (realTransportModel n) m
      (fun q => realParallelTransportFlow g q t) p := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  let K := realParallelTransportFlow g p '' Set.Icc (-|t|) |t|
  have hK : IsCompact K :=
    isCompact_Icc.image (realParallelTransportFlow_contMDiff g p).continuous
  obtain ⟨ε, hε, hreg⟩ := realParallelTransportFlow_uniform_local_contMDiff_order m g hK
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
      ContMDiffAt (realTransportModel n) (realTransportModel n) m
        (fun q => realParallelTransportFlow g q ((k : ℝ) * d)) p := by
    intro k
    induction k with
    | zero =>
        intro hk
        have hfun : (fun q : realTransportBundle M =>
            realParallelTransportFlow g q ((0 : ℕ) * d)) = id := by
          funext q
          simp only [Nat.cast_zero, zero_mul, realParallelTransportFlow_zero, id_eq]
        rw [hfun]
        exact contMDiffAt_id
    | succ k ih =>
        intro hk
        have hk' : k ≤ N + 1 := Nat.le_trans (Nat.le_succ k) hk
        have hpk : realParallelTransportFlow g p ((k : ℝ) * d) ∈ K :=
          ⟨(k : ℝ) * d, abs_le.mp (hstep k hk'), rfl⟩
        have hsmall := hreg _ hpk d (abs_lt.mp hd)
        have hc := hsmall.comp p ((ih hk').prodMk contMDiffAt_const)
        convert hc using 1
        funext q
        simp only [Function.comp_apply, realParallelTransportFlow_add, Nat.cast_add, Nat.cast_one,
          add_mul, one_mul]
  have htime : ((N + 1 : ℕ) : ℝ) * d = t := by
    push_cast
    dsimp [d]
    field_simp
  simpa only [htime] using hiter (N + 1) le_rfl

set_option backward.isDefEq.respectTransparency false in
/-- Global joint C1 dependence of the genuine complete geodesic flow. -/
theorem realParallelTransportFlow_joint_contMDiff_order (m : ℕ) (g : SmoothMetric M) :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    ContMDiff ((realTransportModel n).prod 𝓘(ℝ, ℝ)) (realTransportModel n) m
      (fun q : (realTransportBundle M) × ℝ =>
        realParallelTransportFlow g q.1 q.2) := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  intro q
  obtain ⟨U, hU, hpU, ε, hε, hreg⟩ :=
    realParallelTransportFlow_local_contMDiff_order m g (realParallelTransportFlow g q.1 q.2)
  have hz : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hlocal : ContMDiffAt ((realTransportModel n).prod 𝓘(ℝ, ℝ)) (realTransportModel n) m
      (fun a : (realTransportBundle M) × ℝ =>
        realParallelTransportFlow g a.1 a.2) (realParallelTransportFlow g q.1 q.2, 0) :=
    hreg.contMDiffAt ((hU.prod isOpen_Ioo).mem_nhds ⟨hpU, hz⟩)
  have hfirst : ContMDiffAt ((realTransportModel n).prod 𝓘(ℝ, ℝ)) (realTransportModel n) m
      (fun a : (realTransportBundle M) × ℝ =>
        realParallelTransportFlow g a.1 q.2) q :=
    (realParallelTransportFlow_initial_contMDiffAt_order m g q.1 q.2).comp q contMDiffAt_fst
  have hsecond : ContMDiffAt ((realTransportModel n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) m
      (fun a : (realTransportBundle M) × ℝ => a.2 - q.2) q :=
    (contMDiffAt_snd (I := realTransportModel n) (J := 𝓘(ℝ, ℝ))).sub contMDiffAt_const
  have hlocal' : ContMDiffAt ((realTransportModel n).prod 𝓘(ℝ, ℝ)) (realTransportModel n) m
      (fun a : (realTransportBundle M) × ℝ =>
        realParallelTransportFlow g a.1 a.2) (realParallelTransportFlow g q.1 q.2, q.2 - q.2) := by
    simpa only [sub_self] using hlocal
  have hcomp := hlocal'.comp q (hfirst.prodMk hsecond)
  convert hcomp using 1
  funext a
  simp only [Function.comp_apply, ← realParallelTransportFlow_add, add_sub_cancel]

theorem realParallelTransportFlow_joint_smooth (g : SmoothMetric M) :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    ContMDiff ((realTransportModel n).prod 𝓘(ℝ, ℝ)) (realTransportModel n) ∞
      (fun q : realTransportBundle M × ℝ => realParallelTransportFlow g q.1 q.2) := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  intro p
  exact contMDiffAt_iff_nat.mpr fun m _ => realParallelTransportFlow_joint_contMDiff_order m g p

end Yau.Proofs.C04ChartsAux

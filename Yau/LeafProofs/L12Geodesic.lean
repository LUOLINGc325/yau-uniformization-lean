import Yau.LeafProofs.L12
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal Matrix ContDiff
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem realPhasePoint_realPhaseChart (x : M.Carrier)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (hq : q.proj ∈ (chartAt (ComplexVector n) x).source) :
    realPhasePoint x (realPhaseChart x q) = q := by
  have hp : chartInv x (chartPt x q.proj) = q.proj :=
    (extChartAt (ComplexModel n) x).left_inv (by simpa only [extChartAt_source] using hq)
  apply Bundle.TotalSpace.ext hp
  simp only [realPhasePoint, realPhaseChart]
  rw [hp]
  exact heq_of_eq (realFrameCLM_realTangentCoords x q.proj hq q.2)

/-- A bounded physical kinetic-energy set over a compact set of base points
is compact in the actual tangent-bundle topology. -/
theorem isCompact_realTangentEnergy_sublevel (g : SmoothMetric M)
    {K : Set M.Carrier} (hK : IsCompact K) (A : ℝ) :
    letI := manifold_realSmooth M
    IsCompact {q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier |
      q.proj ∈ K ∧ realTangentEnergy g.form q ≤ A} := by
  classical
  letI := manifold_realSmooth M
  letI := manifold_locallyCompact M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  letI := realRiemannianBundle_continuous g
  let E : M.Carrier → Type := TangentSpace 𝓘(ℝ, ComplexVector n)
  let e := fun x : M.Carrier => trivializationAt (ComplexVector n) E x
  have hlocal : ∀ x : M.Carrier, ∃ C : ℝ, 0 < C ∧ ∃ S : Set M.Carrier,
      S ∈ 𝓝 x ∧ IsCompact S ∧ S ⊆ (e x).baseSet ∧
      ∀ y ∈ S, ‖(e x).continuousLinearMapAt ℝ y‖ ≤ C := by
    intro x
    obtain ⟨C, hC, hbound⟩ := eventually_norm_trivializationAt_lt (ComplexVector n) E x
    obtain ⟨S, hS, hsub, hSc⟩ := local_compact_nhds
      (Filter.inter_mem ((e x).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt (ComplexVector n) E x)) hbound)
    exact ⟨C, hC, S, hS, hSc, fun y hy => (hsub hy).1,
      fun y hy => (hsub hy).2.le⟩
  choose C hC S hSn hSc hSe hSb using hlocal
  obtain ⟨T, _, hcover⟩ := hK.elim_nhds_subcover S (fun x _ => hSn x)
  let B := fun x : M.Carrier => (e x).toOpenPartialHomeomorph.symm ''
    (S x ×ˢ Metric.closedBall (0 : ComplexVector n) (C x * Real.sqrt (max A 0)))
  have hBc : ∀ x : M.Carrier, IsCompact (B x) := by
    intro x
    apply ((hSc x).prod (isCompact_closedBall _ _)).image_of_continuousOn
    apply (e x).toOpenPartialHomeomorph.continuousOn_symm.mono
    intro p hp
    exact (e x).mem_target.mpr (hSe x hp.1)
  apply (T.isCompact_biUnion (fun x _ => hBc x)).of_isClosed_subset
  · exact (hK.isClosed.preimage (FiberBundle.continuous_proj (ComplexVector n) E)).inter
      (isClosed_le (realTangentEnergy_contMDiff g).continuous continuous_const)
  · intro q hq
    obtain ⟨x, hxT, hqx⟩ := Set.mem_iUnion₂.mp (hcover hq.1)
    apply Set.mem_iUnion₂.mpr ⟨x, hxT, ?_⟩
    have hbase : q.proj ∈ (e x).baseSet := hSe x hqx
    have hnorm : ‖q.2‖ ≤ Real.sqrt (max A 0) := by
      apply (Real.le_sqrt (norm_nonneg _) (le_max_right A 0)).mpr
      rw [← realTangentEnergy_eq_norm_sq g.form q]
      exact hq.2.trans (le_max_left A 0)
    refine ⟨e x q, ?_, (e x).toOpenPartialHomeomorph.left_inv ((e x).mem_source.mpr hbase)⟩
    constructor
    · simpa only [(e x).coe_fst' hbase] using hqx
    · rw [Metric.mem_closedBall, dist_zero_right]
      rw [← (e x).continuousLinearMapAt_apply_of_mem (R := ℝ) hbase q.2]
      exact ((e x).continuousLinearMapAt ℝ q.proj).le_opNorm q.2 |>.trans
        (mul_le_mul (hSb x q.proj hqx) hnorm (norm_nonneg _) (hC x).le)

theorem realPhaseChart_change_eventually
    (pA pB : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (q : ComplexVector n × ComplexVector n) (hq : q.1 ∈ chartTarget pA.proj)
    (hB : chartInv pA.proj q.1 ∈ (extChartAt (ComplexModel n) pB.proj).source) :
    letI := manifold_realSmooth M
    (extChartAt (realPhaseModel n) pB ∘ (extChartAt (realPhaseModel n) pA).symm)
      =ᶠ[𝓝 q] realTangentChartChange pA.proj pB.proj := by
  letI := manifold_realSmooth M
  letI := realPhaseModel_boundaryless n
  have hqA : q ∈ (extChartAt (realPhaseModel n) pA).target :=
    (realPhaseChart_target pA q).mpr hq
  have hpB : (extChartAt (realPhaseModel n) pA).symm q ∈
      (extChartAt (realPhaseModel n) pB).source := by
    rw [realPhasePoint_eq_extChartAt_symm pA q hq, realPhaseChart_source]
    simpa only [realPhasePoint, extChartAt_source] using hB
  have hnB : (extChartAt (realPhaseModel n) pA).symm ⁻¹'
      (extChartAt (realPhaseModel n) pB).source ∈ 𝓝 q :=
    (continuousAt_extChartAt_symm'' hqA).preimage_mem_nhds
      ((isOpen_extChartAt_source (I := realPhaseModel n) pB).mem_nhds hpB)
  filter_upwards [(isOpen_extChartAt_target (I := realPhaseModel n) pA).mem_nhds hqA,
    hnB] with r hrA hrB
  have hr : r.1 ∈ chartTarget pA.proj := (realPhaseChart_target pA r).mp hrA
  have hr' : chartInv pA.proj r.1 ∈ (extChartAt (ComplexModel n) pB.proj).source := by
    change (extChartAt (realPhaseModel n) pA).symm r ∈
      (extChartAt (realPhaseModel n) pB).source at hrB
    rw [realPhasePoint_eq_extChartAt_symm pA r hr, realPhaseChart_source] at hrB
    simpa only [realPhasePoint, extChartAt_source] using hrB
  exact realPhaseChart_change pA pB r hr hr'

theorem realPhaseChart_change_fderiv_spray (g : SmoothMetric M)
    (pA pB : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (q : ComplexVector n × ComplexVector n) (hq : q.1 ∈ chartTarget pA.proj)
    (hB : chartInv pA.proj q.1 ∈ (extChartAt (ComplexModel n) pB.proj).source) :
    letI := manifold_realSmooth M
    fderiv ℝ (extChartAt (realPhaseModel n) pB ∘ (extChartAt (realPhaseModel n) pA).symm) q
      (chartGeodesicSpray g.form pA.proj q) =
        chartGeodesicSpray g.form pB.proj (realTangentChartChange pA.proj pB.proj q) := by
  letI := manifold_realSmooth M
  rw [(realPhaseChart_change_eventually pA pB q hq hB).fderiv_eq]
  exact realTangentChartChange_fderiv_spray g pA.proj pB.proj q hq hB

theorem manifold_realPhase (M : ComplexManifold n) :
    letI := manifold_realSmooth M
    IsManifold (realPhaseModel n) ∞ (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) := by
  letI := manifold_realSmooth M
  change IsManifold (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) ∞
    (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
  infer_instance

/-- The Levi--Civita geodesic spray as an actual vector field on the tangent bundle. -/
def realGeodesicSpray (g : SmoothMetric M)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    letI := manifold_realSmooth M
    TangentSpace (realPhaseModel n) q := by
  letI := manifold_realSmooth M
  exact chartGeodesicSpray g.form q.proj (realPhaseChart q.proj q)

theorem realGeodesicSpray_in_phaseChart (g : SmoothMetric M)
    (p q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (hq : q.proj ∈ (chartAt (ComplexVector n) p.proj).source) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    (trivializationAt (ComplexVector n × ComplexVector n)
      (TangentSpace (realPhaseModel n)) p
        (⟨q, realGeodesicSpray g q⟩ : TangentBundle (realPhaseModel n)
          (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier))).2 =
      chartGeodesicSpray g.form p.proj (realPhaseChart p.proj q) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := realPhaseModel_boundaryless n
  have hself : q.proj ∈ (chartAt (ComplexVector n) q.proj).source := mem_chart_source _ _
  have hqa : (realPhaseChart q.proj q).1 ∈ chartTarget q.proj := mem_extChartAt_target _
  have hqb : chartInv q.proj (realPhaseChart q.proj q).1 ∈
      (extChartAt (ComplexModel n) p.proj).source := by
    change (extChartAt (ComplexModel n) q.proj).symm
      (extChartAt (ComplexModel n) q.proj q.proj) ∈ _
    rw [(extChartAt (ComplexModel n) q.proj).left_inv (mem_extChartAt_source _)]
    simpa only [extChartAt_source] using hq
  have hchange := realPhaseChart_change q p (realPhaseChart q.proj q) hqa hqb
  rw [← realPhaseChart_eq_extChartAt q q hself,
    (extChartAt (realPhaseModel n) q).left_inv (mem_extChartAt_source _),
    realPhaseChart_eq_extChartAt p q hq] at hchange
  rw [realPhaseChart_eq_extChartAt q q hself] at hchange
  change fderivWithin ℝ
      (extChartAt (realPhaseModel n) p ∘ (extChartAt (realPhaseModel n) q).symm)
      (Set.range (realPhaseModel n)) (extChartAt (realPhaseModel n) q q)
      (realGeodesicSpray g q) = _
  rw [ModelWithCorners.range_eq_univ, fderivWithin_univ,
    realPhaseChart_eq_extChartAt q q hself]
  change fderiv ℝ
      (extChartAt (realPhaseModel n) p ∘ (extChartAt (realPhaseModel n) q).symm)
      (realPhaseChart q.proj q) (chartGeodesicSpray g.form q.proj (realPhaseChart q.proj q)) = _
  rw [realPhaseChart_change_fderiv_spray g q p _ hqa hqb, ← hchange]

set_option backward.isDefEq.respectTransparency false in
theorem realGeodesicSpray_contMDiff (g : SmoothMetric M) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiff (realPhaseModel n)
      ((realPhaseModel n).prod 𝓘(ℝ, ComplexVector n × ComplexVector n)) ∞
      (fun q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier =>
        (⟨q, realGeodesicSpray g q⟩ : TangentBundle (realPhaseModel n)
          (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier))) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  intro p
  apply (Bundle.contMDiffAt_section (IB := realPhaseModel n)
    (s := realGeodesicSpray g) p).mpr
  have hs := (chartGeodesicSpray_contDiffOn g p.proj).contDiffAt
    (((isOpen_extChartAt_target (I := ComplexModel n) p.proj).prod isOpen_univ).mem_nhds
      (show realPhaseChart p.proj p ∈ chartTarget p.proj ×ˢ Set.univ from
        ⟨mem_extChartAt_target _, Set.mem_univ _⟩))
  have hp : ContMDiffAt (realPhaseModel n) 𝓘(ℝ, ComplexVector n × ComplexVector n) ∞
      (extChartAt (realPhaseModel n) p) p :=
    contMDiffAt_extChartAt
  rw [← realPhaseChart_eq_extChartAt p p (mem_chart_source _ _)] at hs
  have hsp := hs.contMDiffAt.comp p hp
  apply hsp.congr_of_eventuallyEq
  filter_upwards [extChartAt_source_mem_nhds (I := realPhaseModel n) p] with q hq
  have hb := (realPhaseChart_source p q).mp hq
  rw [realGeodesicSpray_in_phaseChart g p q hb]
  exact congrArg (chartGeodesicSpray g.form p.proj)
    (realPhaseChart_eq_extChartAt p q hb).symm

theorem realTangentEnergy_in_phaseChart (h : HermitianField M) (x : M.Carrier)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (hq : q.proj ∈ (chartAt (ComplexVector n) x).source) :
    realTangentEnergy h q = chartGeodesicEnergy h x (realPhaseChart x q) := by
  have hz : (realPhaseChart x q).1 ∈ chartTarget x :=
    (extChartAt (ComplexModel n) x).map_source (by simpa only [extChartAt_source] using hq)
  calc
    _ = realTangentEnergy h (realPhasePoint x (realPhaseChart x q)) :=
      congrArg (realTangentEnergy h) (realPhasePoint_realPhaseChart x q hq).symm
    _ = _ := realTangentEnergy_realPhasePoint h x (realPhaseChart x q) hz

theorem tangentCoordChange_realGeodesicSpray (g : SmoothMetric M)
    (p q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    : letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ∀ (hq : q ∈ (extChartAt (realPhaseModel n) p).source),
    tangentCoordChange (realPhaseModel n) q p q (realGeodesicSpray g q) =
      chartGeodesicSpray g.form p.proj (extChartAt (realPhaseModel n) p q) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  intro hq
  have hbase := (realPhaseChart_source p q).mp hq
  have h := realGeodesicSpray_in_phaseChart g p q hbase
  change tangentCoordChange (realPhaseModel n) q p q (realGeodesicSpray g q) = _ at h
  rw [← realPhaseChart_eq_extChartAt p q hbase] at h
  exact h

theorem exists_local_realGeodesic (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t₀ : ℝ) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ∃ γ : ℝ → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier,
      γ t₀ = p ∧ IsMIntegralCurveAt γ (realGeodesicSpray g) t₀ := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := realPhaseModel_boundaryless n
  exact exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless t₀
    ((realGeodesicSpray_contMDiff g p).of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp))

theorem realGeodesicEnergy_hasDerivAt (g : SmoothMetric M)
    (γ : ℝ → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) {t₀ : ℝ} :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    IsMIntegralCurveAt γ (realGeodesicSpray g) t₀ →
      HasDerivAt (fun t => realTangentEnergy g.form (γ t)) 0 t₀ := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  intro hγ
  let p := γ t₀
  let η := extChartAt (realPhaseModel n) p ∘ γ
  have hη := hγ.eventually_hasDerivAt.self_of_nhds
  rw [tangentCoordChange_realGeodesicSpray g p p (mem_extChartAt_source p)] at hη
  have hz : (η t₀).1 ∈ chartTarget p.proj :=
    (realPhaseChart_target p (η t₀)).mp (mem_extChartAt_target p)
  have hE := chartGeodesicEnergy_hasDerivAt g p.proj η hz hη
  apply hE.congr_of_eventuallyEq
  filter_upwards [hγ.continuousAt.preimage_mem_nhds
    (extChartAt_source_mem_nhds (I := realPhaseModel n) p)] with t ht
  have hbase := (realPhaseChart_source p (γ t)).mp ht
  rw [realTangentEnergy_in_phaseChart g.form p.proj (γ t) hbase]
  exact congrArg (chartGeodesicEnergy g.form p.proj)
    (realPhaseChart_eq_extChartAt p (γ t) hbase).symm

theorem realGeodesicEnergy_constant (g : SmoothMetric M)
    (γ : ℝ → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) {a b s t : ℝ} :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    IsMIntegralCurveOn γ (realGeodesicSpray g) (Set.Ioo a b) →
      s ∈ Set.Ioo a b → t ∈ Set.Ioo a b →
        realTangentEnergy g.form (γ s) = realTangentEnergy g.form (γ t) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  intro hγ hs ht
  apply isOpen_Ioo.is_const_of_deriv_eq_zero
    (f := fun r => realTangentEnergy g.form (γ r)) (convex_Ioo a b).isPreconnected
  · intro r hr
    exact (realGeodesicEnergy_hasDerivAt g γ
      (hγ.isMIntegralCurveAt (Ioo_mem_nhds hr.1 hr.2))).differentiableAt.differentiableWithinAt
  · intro r hr
    exact (realGeodesicEnergy_hasDerivAt g γ
      (hγ.isMIntegralCurveAt (Ioo_mem_nhds hr.1 hr.2))).deriv
  · exact hs
  · exact ht

end Yau.LeafProofs.L12Aux

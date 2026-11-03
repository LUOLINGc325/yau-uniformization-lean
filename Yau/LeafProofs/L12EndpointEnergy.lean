import Yau.LeafProofs.L12EndpointBranch
import Yau.LeafProofs.L12NormalDistance

/-! First variation of the actual segment energy on a two-endpoint
geodesic branch. Only C1 dependence of the genuine flow is used. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

/-- Energy of the actual geodesic segment, with its given duration. -/
def realSegmentEnergy (g : SmoothMetric M) (d : ℝ)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) : ℝ :=
  d / 2 * realTangentEnergy g.form q

/-- Initial phase of the same segment traversed backwards. -/
def realSegmentReverse (g : SmoothMetric M) (d : ℝ)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier :=
  realPhaseScale (-1) (realGeodesicFlow g q d)

theorem realSegmentEnergy_contMDiff (g : SmoothMetric M) (d : ℝ) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiff (realPhaseModel n) 𝓘(ℝ, ℝ) 1 (realSegmentEnergy g d) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  exact contMDiff_const.mul ((realTangentEnergy_contMDiff g).of_le (by simp))

theorem realSegmentReverse_contMDiff (g : SmoothMetric M) (d : ℝ) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiff (realPhaseModel n) (realPhaseModel n) 1 (realSegmentReverse g d) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  exact ((realPhaseScale_contMDiff (M := M) (-1)).of_le (by simp)).comp
    ((realGeodesicFlow_joint_contMDiff g).comp
      (contMDiff_id.prodMk (contMDiff_const (c := d))))

theorem realSegmentReverse_terminal (g : SmoothMetric M) (d : ℝ)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    realGeodesicFlow g (realSegmentReverse g d q) d = realPhaseScale (-1) q := by
  rw [realSegmentReverse, realGeodesicFlow_rescale]
  simp only [mul_neg_one, realGeodesicFlow_neg]

theorem realSegmentEnergy_reverse (g : SmoothMetric M) (d : ℝ)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    realSegmentEnergy g d (realSegmentReverse g d q) = realSegmentEnergy g d q := by
  have h (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
      realTangentEnergy g.form (realPhaseScale (-1) p) = realTangentEnergy g.form p := by
    change ((underlyingRealRiemannianMetric g.form).inner p.proj)
      ((-1 : ℝ) • p.2) ((-1 : ℝ) • p.2) = _
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    change (-1 : ℝ) * (-1 * realTangentEnergy g.form p) = _
    ring
  dsimp only [realSegmentEnergy, realSegmentReverse]
  rw [h, realGeodesicFlow_energy]

theorem realSegmentReverse_endpointMap (g : SmoothMetric M) (d : ℝ)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    realGeodesicEndpointMap g d (realSegmentReverse g d q) =
      ((realGeodesicFlow g q d).proj, q.proj) := by
  apply Prod.ext
  · rfl
  · change (realGeodesicFlow g (realSegmentReverse g d q) d).proj = q.proj
    rw [realSegmentReverse_terminal]
    rfl

theorem realSegmentReverse_involutive (g : SmoothMetric M) (d : ℝ)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    realSegmentReverse g d (realSegmentReverse g d q) = q := by
  change realPhaseScale (-1) (realGeodesicFlow g (realSegmentReverse g d q) d) = q
  rw [realSegmentReverse_terminal]
  cases q with | mk x v =>
    change (⟨x, (-1 : ℝ) • ((-1 : ℝ) • v)⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) = ⟨x, v⟩
    simp only [smul_smul, neg_mul, one_mul, neg_neg, one_smul]

/-- Gauss' lemma is the differential of the actual fixed-base energy. -/
theorem realSegmentEnergy_fiber_hasFDerivAt (g : SmoothMetric M) (d : ℝ)
    (x y : M.Carrier) (v : TangentSpace 𝓘(ℝ, ComplexVector n) x)
    (hy : realVelocityBaseFlow g x v d ∈ (chartAt (ComplexVector n) y).source) :
    letI := manifold_realSmooth M
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    letI := underlyingRealTangentInnerProductSpace g.form x
    HasFDerivAt (fun w : TangentSpace 𝓘(ℝ, ComplexVector n) x =>
      realSegmentEnergy g d (⟨x, w⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier))
      ((realMetricInChart g.form y (chartPt y (realGeodesicFlow g
          (⟨x, v⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) d).proj)
        (realTangentCoords y (realGeodesicFlow g
          (⟨x, v⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) d).proj
          (realGeodesicFlow g (⟨x, v⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) d).2)).comp
        (fderiv ℝ (fun w => chartPt y (realVelocityBaseFlow g x w d)) v)) v := by
  letI := manifold_realSmooth M
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  let B := (underlyingRealRiemannianMetric g.form).inner x
  have hD := (B.hasFDerivAt.clm_apply (hasFDerivAt_id v)).const_mul (d / 2)
  convert hD using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro w
    have hG := realRadialJacobiPairing_eq g
      (⟨x, v⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) w d
    rw [realRadialJacobiPairing_in_chart g _ w y d hy,
      realGeodesicJacobiField_in_chart g _ w d y hy] at hG
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
    change _ = d * B v w at hG
    rw [hG]
    simp only [id_eq]
    have hs := (underlyingRealRiemannianMetric g.form).symm x w v
    dsimp only [B]
    rw [hs]
    ring

/-- A C1 phase variation whose initial point stays fixed satisfies the
terminal endpoint first-variation formula in every endpoint chart. -/
theorem realSegmentEnergy_fixedBase_hasFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : SmoothMetric M) (d : ℝ)
    (Q : E → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (z : E) (y : M.Carrier) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiffAt 𝓘(ℝ, E) (realPhaseModel n) 1 Q z →
    (∀ᶠ u in 𝓝 z, (Q u).proj = (Q z).proj) →
    (realGeodesicFlow g (Q z) d).proj ∈ (chartAt (ComplexVector n) y).source →
    HasFDerivAt (realSegmentEnergy g d ∘ Q)
      ((realMetricInChart g.form y (chartPt y (realGeodesicFlow g (Q z) d).proj)
        (realTangentCoords y (realGeodesicFlow g (Q z) d).proj (realGeodesicFlow g (Q z) d).2)).comp
        (fderiv ℝ (fun u => chartPt y (realGeodesicFlow g (Q u) d).proj) z)) z := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  intro hQ hbase hy
  let x := (Q z).proj
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  let C := extChartAt (realPhaseModel n) (Q z)
  let w : E → TangentSpace 𝓘(ℝ, ComplexVector n) x :=
    fun u => realFrameCLM x x (C (Q u)).2
  have hC : ContMDiffAt (realPhaseModel n) 𝓘(ℝ, ComplexVector n × ComplexVector n) 1 C (Q z) :=
    contMDiffAt_extChartAt
  have hw : DifferentiableAt ℝ w z :=
    ((realFrameCLM x x).differentiableAt).comp z
      ((hC.comp z hQ).contDiffAt.differentiableAt (by simp)).snd
  have heq : (fun u => (⟨x, w u⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)) =ᶠ[𝓝 z] Q := by
    filter_upwards [hbase] with u hu
    have hsrc : (Q u).proj ∈ (chartAt (ComplexVector n) x).source := by
      rw [hu]
      exact mem_chart_source _ _
    have hcoord : C (Q u) = realPhaseChart x (Q u) :=
      realPhaseChart_eq_extChartAt (Q z) (Q u) hsrc
    dsimp only [w]
    rw [hcoord]
    change (⟨x, realFrameCLM x x (realTangentCoords x (Q u).proj (Q u).2)⟩ :
      TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) = Q u
    have hu' : (Q u).proj = x := hu
    generalize hqu : Q u = p at hu' ⊢
    cases p with | mk b v =>
      dsimp at hu'
      subst b
      rw [realFrameCLM_realTangentCoords x x (mem_chart_source _ _)]
  have heq₀ := heq.eq_of_nhds
  have hflow : DifferentiableAt ℝ
      (fun v : TangentSpace 𝓘(ℝ, ComplexVector n) x => chartPt y (realVelocityBaseFlow g x v d)) (w z) := by
    have hsrc : realVelocityBaseFlow g x (w z) d ∈ (chartAt (ComplexVector n) y).source := by
      change (realGeodesicFlow g _ d).proj ∈ _
      rw [heq₀]
      exact hy
    have hchart : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1
        (chartPt y) (realVelocityBaseFlow g x (w z) d) := contMDiffAt_extChartAt' hsrc
    exact (hchart.comp (w z) (realVelocityBaseFlow_contMDiff g x d (w z))).contDiffAt.differentiableAt (by simp)
  have hf := (realSegmentEnergy_fiber_hasFDerivAt g d x y (w z) (by
    change (realGeodesicFlow g _ d).proj ∈ _
    rw [heq₀]
    exact hy)).comp z hw.hasFDerivAt
  have hcoord := hflow.hasFDerivAt.comp z hw.hasFDerivAt
  have hcoordEq : (fun u => chartPt y (realVelocityBaseFlow g x (w u) d)) =ᶠ[𝓝 z]
      (fun u => chartPt y (realGeodesicFlow g (Q u) d).proj) := by
    filter_upwards [heq] with u hu
    change chartPt y (realGeodesicFlow g _ d).proj = _
    rw [hu]
  have hDf := (hcoordEq.hasFDerivAt_iff.mp hcoord).fderiv
  have henergyEq : (fun u => realSegmentEnergy g d
      (⟨x, w u⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)) =ᶠ[𝓝 z]
      (realSegmentEnergy g d ∘ Q) := heq.fun_comp (realSegmentEnergy g d)
  have hf' := henergyEq.hasFDerivAt_iff.mp hf
  rw [ContinuousLinearMap.comp_assoc, ← hDf] at hf'
  have ht := congrArg (fun p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier =>
    realTangentCoords y (realGeodesicFlow g p d).proj (realGeodesicFlow g p d).2) heq₀
  rw [ht] at hf'
  simpa only [heq₀] using hf'

/-- The metric dual of the actual phase velocity in a specified chart. -/
def realChartMomentum (g : SmoothMetric M) (y : M.Carrier)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) : ComplexVector n →L[ℝ] ℝ :=
  realMetricInChart g.form y (chartPt y q.proj) (realTangentCoords y q.proj q.2)

/-- Momentum coordinates are smooth functions of the genuine phase;
C1 flow and a C1 branch therefore give C1 gradient coefficients. -/
theorem realChartMomentum_contMDiffAt (g : SmoothMetric M) (y : M.Carrier)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (hy : q.proj ∈ (chartAt (ComplexVector n) y).source) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiffAt (realPhaseModel n) 𝓘(ℝ, ComplexVector n →L[ℝ] ℝ) ∞
      (realChartMomentum g y) q := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  let r : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier := ⟨y, 0⟩
  let C := extChartAt (realPhaseModel n) r
  have hs : q ∈ C.source := (realPhaseChart_source r q).mpr hy
  have hC : ContMDiffAt (realPhaseModel n) 𝓘(ℝ, ComplexVector n × ComplexVector n) ∞ C q :=
    contMDiffAt_extChartAt' (by simpa only [C, extChartAt_source] using hs)
  have htarget : (C q).1 ∈ chartTarget y :=
    (realPhaseChart_target r (C q)).mp (C.map_source hs)
  let H : ComplexVector n × ComplexVector n → ComplexVector n →L[ℝ] ℝ :=
    fun u => realMetricInChart g.form y u.1 u.2
  have hH : ContDiffAt ℝ ∞ H (C q) :=
    (((realMetricInChart_smooth g y).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) y).mem_nhds htarget)).comp
        (C q) contDiffAt_fst).clm_apply contDiffAt_snd
  apply (hH.contMDiffAt.comp q hC).congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_source (I := realPhaseModel n) r).mem_nhds hs] with p hp
  change realMetricInChart g.form y (chartPt y p.proj) (realTangentCoords y p.proj p.2) = H (C p)
  have hc := realPhaseChart_eq_extChartAt r p ((realPhaseChart_source r p).mp hp)
  rw [hc]
  rfl

theorem realChartMomentum_neg (g : SmoothMetric M) (y : M.Carrier)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    realChartMomentum g y (realPhaseScale (-1) q) = -realChartMomentum g y q := by
  change realMetricInChart g.form y (chartPt y q.proj)
    (realTangentCoords y q.proj ((-1 : ℝ) • q.2)) = _
  simp only [map_smul]
  exact neg_one_smul ℝ (realChartMomentum g y q)

/-- Reversal gives the negative initial endpoint differential without
any higher regularity of the initial-data flow. -/
theorem realSegmentEnergy_fixedTerminal_hasFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : SmoothMetric M) (d : ℝ)
    (Q : E → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (z : E) (y : M.Carrier) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiffAt 𝓘(ℝ, E) (realPhaseModel n) 1 Q z →
    (∀ᶠ u in 𝓝 z, (realGeodesicFlow g (Q u) d).proj = (realGeodesicFlow g (Q z) d).proj) →
    (Q z).proj ∈ (chartAt (ComplexVector n) y).source →
    HasFDerivAt (realSegmentEnergy g d ∘ Q)
      ((-realChartMomentum g y (Q z)).comp
        (fderiv ℝ (fun u => chartPt y (Q u).proj) z)) z := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  intro hQ hbase hy
  let R := realSegmentReverse g d ∘ Q
  have hR : ContMDiffAt 𝓘(ℝ, E) (realPhaseModel n) 1 R z :=
    (realSegmentReverse_contMDiff g d (Q z)).comp z hQ
  have h := realSegmentEnergy_fixedBase_hasFDerivAt g d R z y hR hbase (by
    change (realGeodesicFlow g (realSegmentReverse g d (Q z)) d).proj ∈ _
    rw [realSegmentReverse_terminal]
    exact hy)
  change HasFDerivAt (realSegmentEnergy g d ∘ R)
    ((realChartMomentum g y (realGeodesicFlow g (R z) d)).comp
      (fderiv ℝ (fun u => chartPt y (realGeodesicFlow g (R u) d).proj) z)) z at h
  have hcoord : (fun u => chartPt y (realGeodesicFlow g (R u) d).proj) =
      (fun u => chartPt y (Q u).proj) := by
    funext u
    dsimp only [R, Function.comp_apply]
    rw [realSegmentReverse_terminal]
    rfl
  have henergy : realSegmentEnergy g d ∘ R = realSegmentEnergy g d ∘ Q := by
    funext u
    exact realSegmentEnergy_reverse g d (Q u)
  rw [henergy, hcoord] at h
  dsimp only [R, Function.comp_apply] at h
  rw [realSegmentReverse_terminal, realChartMomentum_neg] at h
  exact h

/-- Two endpoint first variation for an arbitrary C1 geodesic branch in
endpoint coordinates. Its covectors are the actual initial and terminal
velocities paired by the actual metric. -/
theorem realSegmentEnergy_endpointChart_hasFDerivAt
    (g : SmoothMetric M) (d : ℝ) (a₀ b₀ : M.Carrier)
    (Q : ComplexVector n × ComplexVector n → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (z : ComplexVector n × ComplexVector n)
    (ha : z.1 ∈ chartTarget a₀) (hb : z.2 ∈ chartTarget b₀) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiffAt 𝓘(ℝ, ComplexVector n × ComplexVector n) (realPhaseModel n) 1 Q z →
    (∀ᶠ u in 𝓝 z, (Q u).proj = chartInv a₀ u.1 ∧
      (realGeodesicFlow g (Q u) d).proj = chartInv b₀ u.2) →
    HasFDerivAt (realSegmentEnergy g d ∘ Q)
      ((-realChartMomentum g a₀ (Q z)).coprod
        (realChartMomentum g b₀ (realGeodesicFlow g (Q z) d))) z := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  intro hQ hends
  have hz := hends.self_of_nhds
  have hasrc : (Q z).proj ∈ (chartAt (ComplexVector n) a₀).source := by
    rw [hz.1]
    simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) a₀).map_target ha
  have hbsrc : (realGeodesicFlow g (Q z) d).proj ∈ (chartAt (ComplexVector n) b₀).source := by
    rw [hz.2]
    simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) b₀).map_target hb
  let f := realSegmentEnergy g d ∘ Q
  have hf : DifferentiableAt ℝ f z :=
    ((realSegmentEnergy_contMDiff g d (Q z)).comp z hQ).contDiffAt.differentiableAt (by simp)
  let iL : ComplexVector n → ComplexVector n × ComplexVector n := fun u => (u, z.2)
  let iR : ComplexVector n → ComplexVector n × ComplexVector n := fun u => (z.1, u)
  have hiL : ContDiffAt ℝ 1 iL z.1 := contDiffAt_id.prodMk contDiffAt_const
  have hiR : ContDiffAt ℝ 1 iR z.2 := contDiffAt_const.prodMk contDiffAt_id
  have hQL : ContMDiffAt 𝓘(ℝ, ComplexVector n) (realPhaseModel n) 1 (Q ∘ iL) z.1 :=
    hQ.comp z.1 hiL.contMDiffAt
  have hQR : ContMDiffAt 𝓘(ℝ, ComplexVector n) (realPhaseModel n) 1 (Q ∘ iR) z.2 :=
    hQ.comp z.2 hiR.contMDiffAt
  have hendsL := hiL.continuousAt.eventually hends
  have hendsR := hiR.continuousAt.eventually hends
  have hL := realSegmentEnergy_fixedTerminal_hasFDerivAt g d (Q ∘ iL) z.1 a₀ hQL (by
    filter_upwards [hendsL] with u hu
    exact hu.2.trans hz.2.symm) hasrc
  have hR := realSegmentEnergy_fixedBase_hasFDerivAt g d (Q ∘ iR) z.2 b₀ hQR (by
    filter_upwards [hendsR] with u hu
    exact hu.1.trans hz.1.symm) hbsrc
  have heL : (fun u => chartPt a₀ ((Q ∘ iL) u).proj) =ᶠ[𝓝 z.1] id := by
    filter_upwards [hendsL, (isOpen_extChartAt_target (I := ComplexModel n) a₀).mem_nhds ha] with u hu hut
    dsimp only [Function.comp_apply]
    rw [hu.1]
    exact (extChartAt (ComplexModel n) a₀).right_inv hut
  have heR : (fun u => chartPt b₀ (realGeodesicFlow g ((Q ∘ iR) u) d).proj) =ᶠ[𝓝 z.2] id := by
    filter_upwards [hendsR, (isOpen_extChartAt_target (I := ComplexModel n) b₀).mem_nhds hb] with u hu hut
    dsimp only [Function.comp_apply]
    rw [hu.2]
    exact (extChartAt (ComplexModel n) b₀).right_inv hut
  rw [heL.fderiv_eq, fderiv_id, ContinuousLinearMap.comp_id] at hL
  rw [heR.fderiv_eq, fderiv_id, ContinuousLinearMap.comp_id] at hR
  have hLinL : HasFDerivAt iL (ContinuousLinearMap.inl ℝ (ComplexVector n) (ComplexVector n)) z.1 :=
    hasFDerivAt_prodMk_left z.1 z.2
  have hLinR : HasFDerivAt iR (ContinuousLinearMap.inr ℝ (ComplexVector n) (ComplexVector n)) z.2 :=
    hasFDerivAt_prodMk_right z.1 z.2
  have hDL := (hf.hasFDerivAt.comp z.1 hLinL).unique hL
  have hDR := (hf.hasFDerivAt.comp z.2 hLinR).unique hR
  have hD : fderiv ℝ f z = (-realChartMomentum g a₀ (Q z)).coprod
      (realChartMomentum g b₀ (realGeodesicFlow g (Q z) d)) := by
    apply ContinuousLinearMap.prod_ext
    · simpa using hDL
    · simpa [realChartMomentum] using hDR
  rw [← hD]
  exact hf.hasFDerivAt

/-- Both endpoint gradient coefficients depend C1 on every C1 phase
branch. This uses only the joint C1 geodesic flow. -/
theorem realSegmentEnergy_endpointGradient_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : SmoothMetric M) (d : ℝ) (a₀ b₀ : M.Carrier)
    (Q : E → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (z : E)
    (ha : (Q z).proj ∈ (chartAt (ComplexVector n) a₀).source)
    (hb : (realGeodesicFlow g (Q z) d).proj ∈ (chartAt (ComplexVector n) b₀).source) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiffAt 𝓘(ℝ, E) (realPhaseModel n) 1 Q z →
    ContDiffAt ℝ 1 (fun u => (-realChartMomentum g a₀ (Q u)).coprod
      (realChartMomentum g b₀ (realGeodesicFlow g (Q u) d))) z := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  intro hQ
  have hL : ContDiffAt ℝ 1 (fun u => -realChartMomentum g a₀ (Q u)) z :=
    (((realChartMomentum_contMDiffAt g a₀ (Q z) ha).of_le (by simp)).comp z hQ).contDiffAt.neg
  have hF : ContMDiffAt 𝓘(ℝ, E) (realPhaseModel n) 1 (fun u => realGeodesicFlow g (Q u) d) z :=
    (realGeodesicFlow_joint_contMDiff g (Q z, d)).comp z (hQ.prodMk contMDiffAt_const)
  have hRm : ContMDiffAt (realPhaseModel n) 𝓘(ℝ, ComplexVector n →L[ℝ] ℝ) 1
      (realChartMomentum g b₀) (realGeodesicFlow g (Q z) d) :=
    (realChartMomentum_contMDiffAt g b₀ (realGeodesicFlow g (Q z) d) hb).of_le (by simp)
  have hRmd := hRm.comp z hF
  have hR : ContDiffAt ℝ 1 (fun u => realChartMomentum g b₀ (realGeodesicFlow g (Q u) d)) z :=
    hRmd.contDiffAt
  change ContDiffAt ℝ 1 (fun u =>
    (-realChartMomentum g a₀ (Q u)).comp (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)) +
    (realChartMomentum g b₀ (realGeodesicFlow g (Q u) d)).comp
      (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n))) z
  exact (hL.clm_comp contDiffAt_const).add (hR.clm_comp contDiffAt_const)

/-- The coordinate energy of any actual C1 endpoint branch has the two
endpoint gradient given by its genuine initial and terminal velocities. -/
theorem realSegmentEnergy_endpointBranch_hasFDerivAt
    (g : SmoothMetric M) (d : ℝ) (U : Set (M.Carrier × M.Carrier)) (hU : IsOpen U)
    (P : M.Carrier × M.Carrier → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (a₀ b₀ : M.Carrier) (z : ComplexVector n × ComplexVector n)
    (ha : z.1 ∈ chartTarget a₀) (hb : z.2 ∈ chartTarget b₀)
    (hz : (chartInv a₀ z.1, chartInv b₀ z.2) ∈ U) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiffOn (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) (realPhaseModel n) 1 P U →
    (∀ u ∈ U, (P u).proj = u.1 ∧ (realGeodesicFlow g (P u) d).proj = u.2) →
    HasFDerivAt
      (fun u : ComplexVector n × ComplexVector n =>
        realSegmentEnergy g d (P (chartInv a₀ u.1, chartInv b₀ u.2)))
      ((-realMetricInChart g.form a₀ z.1
          (realTangentCoords a₀ (P (chartInv a₀ z.1, chartInv b₀ z.2)).proj
            (P (chartInv a₀ z.1, chartInv b₀ z.2)).2)).coprod
        (realMetricInChart g.form b₀ z.2
          (realTangentCoords b₀ (realGeodesicFlow g (P (chartInv a₀ z.1, chartInv b₀ z.2)) d).proj
            (realGeodesicFlow g (P (chartInv a₀ z.1, chartInv b₀ z.2)) d).2))) z := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  intro hP hends
  let χ : ComplexVector n × ComplexVector n → M.Carrier × M.Carrier :=
    fun u => (chartInv a₀ u.1, chartInv b₀ u.2)
  let Q := P ∘ χ
  have hχ : ContMDiffAt 𝓘(ℝ, ComplexVector n × ComplexVector n)
      (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) 1 χ z :=
    (((contMDiffAt_chartInv_real a₀ z.1 ha).of_le (by simp)).comp z
      (contDiffAt_fst.contMDiffAt)).prodMk
        (((contMDiffAt_chartInv_real b₀ z.2 hb).of_le (by simp)).comp z
          (contDiffAt_snd.contMDiffAt))
  have hQ : ContMDiffAt 𝓘(ℝ, ComplexVector n × ComplexVector n) (realPhaseModel n) 1 Q z :=
    (hP.contMDiffAt (hU.mem_nhds hz)).comp z hχ
  have hQends : ∀ᶠ u in 𝓝 z, (Q u).proj = chartInv a₀ u.1 ∧
      (realGeodesicFlow g (Q u) d).proj = chartInv b₀ u.2 := by
    filter_upwards [hχ.continuousAt.eventually (hU.mem_nhds hz)] with u hu
    exact hends (χ u) hu
  have h := realSegmentEnergy_endpointChart_hasFDerivAt g d a₀ b₀ Q z ha hb hQ hQends
  have hca : chartPt a₀ (Q z).proj = z.1 := by
    rw [hQends.self_of_nhds.1]
    exact (extChartAt (ComplexModel n) a₀).right_inv ha
  have hcb : chartPt b₀ (realGeodesicFlow g (Q z) d).proj = z.2 := by
    rw [hQends.self_of_nhds.2]
    exact (extChartAt (ComplexModel n) b₀).right_inv hb
  dsimp only [realChartMomentum] at h
  rw [hca, hcb] at h
  exact h

end Yau.LeafProofs.L12Aux

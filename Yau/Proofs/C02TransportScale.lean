import Yau.Proofs.C02ParallelSmooth

/-! Actual velocity rescaling on the transport bundle. The transported vector
is unchanged, and the physical geodesic velocity is scaled. -/

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

def transportVelocityScale (c : ℝ) (q : realTransportBundle M) : realTransportBundle M :=
  ⟨q.proj, (c • q.2.1, q.2.2)⟩

def transportScaleCLM (n : ℕ) (c : ℝ) :
    (ComplexVector n × (ComplexVector n × ComplexVector n)) →L[ℝ]
      (ComplexVector n × (ComplexVector n × ComplexVector n)) :=
  (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n × ComplexVector n)).prod
    (((c • ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)).prod
      (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n))).comp
        (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n × ComplexVector n)))

theorem transportScaleCLM_apply (c : ℝ)
    (q : ComplexVector n × (ComplexVector n × ComplexVector n)) :
    transportScaleCLM n c q = (q.1, (c • q.2.1, q.2.2)) := rfl

theorem realTransportChart_scale (c : ℝ) (x : M.Carrier) (q : realTransportBundle M) :
    realTransportChart x (transportVelocityScale c q) =
      transportScaleCLM n c (realTransportChart x q) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact (realTangentCoords x q.proj).map_smul c q.2.1
    · rfl

theorem transportScale_realTransportPoint (c : ℝ) (x : M.Carrier)
    (q : ComplexVector n × (ComplexVector n × ComplexVector n)) :
    transportVelocityScale c (realTransportPoint x q) =
      realTransportPoint x (transportScaleCLM n c q) := by
  change (⟨chartInv x q.1,
      (c • realFrameCLM x (chartInv x q.1) q.2.1, realFrameCLM x (chartInv x q.1) q.2.2)⟩ :
        realTransportBundle M) =
    ⟨chartInv x q.1,
      (realFrameCLM x (chartInv x q.1) (c • q.2.1), realFrameCLM x (chartInv x q.1) q.2.2)⟩
  rw [map_smul]

theorem transportVelocityScale_eventually_chart (c : ℝ) (p : realTransportBundle M) :
    letI := manifold_realSmooth M
    transportVelocityScale c =ᶠ[𝓝 p]
      ((extChartAt (realTransportModel n) p).symm ∘ transportScaleCLM n c ∘
        extChartAt (realTransportModel n) p) := by
  letI := manifold_realSmooth M
  filter_upwards [extChartAt_source_mem_nhds (I := realTransportModel n) p] with q hq
  have hbase := (realTransportChart_source p q).mp hq
  have hz : (transportScaleCLM n c (realTransportChart p.proj q)).1 ∈ chartTarget p.proj :=
    (extChartAt (ComplexModel n) p.proj).map_source
      (by simpa only [extChartAt_source] using hbase)
  change transportVelocityScale c q = (extChartAt (realTransportModel n) p).symm
    (transportScaleCLM n c (extChartAt (realTransportModel n) p q))
  rw [realTransportChart_eq_extChartAt p q hbase,
    realTransportPoint_eq_extChartAt_symm p _ hz,
    ← transportScale_realTransportPoint, realTransportPoint_realTransportChart p.proj q hbase]

theorem transportVelocityScale_smooth (c : ℝ) :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    ContMDiff (realTransportModel n) (realTransportModel n) ∞
      (transportVelocityScale (M := M) c) := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  letI := realTransportModel_boundaryless n
  intro p
  have hz : transportScaleCLM n c (extChartAt (realTransportModel n) p p) ∈
      (extChartAt (realTransportModel n) p).target := by
    apply (realTransportChart_target p _).mpr
    rw [realTransportChart_eq_extChartAt p p (mem_chart_source _ _)]
    exact mem_extChartAt_target p.proj
  have hi := contMDiffWithinAt_extChartAt_symm_range (I := realTransportModel n) (n := ∞) p hz
  rw [ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ] at hi
  have hm : ContMDiff 𝓘(ℝ, ComplexVector n × (ComplexVector n × ComplexVector n))
      𝓘(ℝ, ComplexVector n × (ComplexVector n × ComplexVector n)) ∞ (transportScaleCLM n c) :=
    (transportScaleCLM n c).contDiff.contMDiff
  have hp : ContMDiffAt (realTransportModel n)
      𝓘(ℝ, ComplexVector n × (ComplexVector n × ComplexVector n)) ∞
      (extChartAt (realTransportModel n) p) p := contMDiffAt_extChartAt
  exact (hi.comp p ((hm _).comp p hp)).congr_of_eventuallyEq
    (transportVelocityScale_eventually_chart c p)

theorem mfderiv_transportVelocityScale (c : ℝ) (p : realTransportBundle M) :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    mfderiv (realTransportModel n) (realTransportModel n) (transportVelocityScale c) p =
      transportScaleCLM n c := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  letI := realTransportModel_boundaryless n
  have hf := (transportVelocityScale_smooth (M := M) c p).mdifferentiableAt (by simp)
  have heq : writtenInExtChartAt (realTransportModel n) (realTransportModel n) p
      (transportVelocityScale c) =ᶠ[𝓝 (extChartAt (realTransportModel n) p p)] transportScaleCLM n c := by
    filter_upwards [(isOpen_extChartAt_target (I := realTransportModel n) p).mem_nhds
      (mem_extChartAt_target p)] with q hq
    have hz := (realTransportChart_target p q).mp hq
    have hz' : (transportScaleCLM n c q).1 ∈ chartTarget p.proj := hz
    have hs : (realTransportPoint p.proj (transportScaleCLM n c q)).proj ∈
        (chartAt (ComplexVector n) p.proj).source := by
      simpa only [realTransportPoint, extChartAt_source, chartInv] using
        (extChartAt (ComplexModel n) p.proj).map_target hz'
    change extChartAt (realTransportModel n) p
      (transportVelocityScale c ((extChartAt (realTransportModel n) p).symm q)) = transportScaleCLM n c q
    rw [realTransportPoint_eq_extChartAt_symm p q hz, transportScale_realTransportPoint,
      realTransportChart_eq_extChartAt p _ hs]
    exact realTransportChart_realTransportPoint p.proj _ hz'
  rw [hf.mfderiv_abuse, ModelWithCorners.range_eq_univ, fderivWithin_univ,
    heq.fderiv_eq, (transportScaleCLM n c).hasFDerivAt.fderiv]

end Yau.Blueprint.C02Proof

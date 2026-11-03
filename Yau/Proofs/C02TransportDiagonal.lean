import Yau.Proofs.C02TransportScale
import Yau.Proofs.C02NormalMap

/-! Duplicating the actual geodesic velocity gives a genuine transport
trajectory, since a geodesic's velocity is parallel. -/

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

def phaseDuplicate (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) : realTransportBundle M :=
  ⟨q.proj, (q.2, q.2)⟩

def phaseDuplicateCLM (n : ℕ) :
    (ComplexVector n × ComplexVector n) →L[ℝ] (ComplexVector n × (ComplexVector n × ComplexVector n)) :=
  (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)).prod
    ((ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n)).prod
      (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n)))

theorem phaseDuplicateCLM_apply (q : ComplexVector n × ComplexVector n) :
    phaseDuplicateCLM n q = (q.1, (q.2, q.2)) := rfl

theorem realTransportChart_duplicate (x : M.Carrier)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    realTransportChart x (phaseDuplicate q) = phaseDuplicateCLM n (realPhaseChart x q) := rfl

theorem phaseDuplicate_realPhasePoint (x : M.Carrier) (q : ComplexVector n × ComplexVector n) :
    phaseDuplicate (realPhasePoint x q) = realTransportPoint x (phaseDuplicateCLM n q) := rfl

theorem phaseDuplicate_eventually_chart
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    letI := manifold_realSmooth M
    phaseDuplicate =ᶠ[𝓝 p]
      ((extChartAt (realTransportModel n) (phaseDuplicate p)).symm ∘ phaseDuplicateCLM n ∘
        extChartAt (realPhaseModel n) p) := by
  letI := manifold_realSmooth M
  filter_upwards [extChartAt_source_mem_nhds (I := realPhaseModel n) p] with q hq
  have hbase := (realPhaseChart_source p q).mp hq
  have hz : (phaseDuplicateCLM n (realPhaseChart p.proj q)).1 ∈ chartTarget p.proj :=
    (extChartAt (ComplexModel n) p.proj).map_source
      (by simpa only [extChartAt_source] using hbase)
  change phaseDuplicate q = (extChartAt (realTransportModel n) (phaseDuplicate p)).symm
    (phaseDuplicateCLM n (extChartAt (realPhaseModel n) p q))
  rw [realPhaseChart_eq_extChartAt p q hbase,
    realTransportPoint_eq_extChartAt_symm (phaseDuplicate p) _ hz,
    ← phaseDuplicate_realPhasePoint]
  change phaseDuplicate q = phaseDuplicate (realPhasePoint p.proj (realPhaseChart p.proj q))
  rw [realPhasePoint_realPhaseChart p.proj q hbase]

theorem phaseDuplicate_smooth :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := manifold_realTransport M
    ContMDiff (realPhaseModel n) (realTransportModel n) ∞ (phaseDuplicate (M := M)) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := manifold_realTransport M
  letI := realTransportModel_boundaryless n
  intro p
  have hz : phaseDuplicateCLM n (extChartAt (realPhaseModel n) p p) ∈
      (extChartAt (realTransportModel n) (phaseDuplicate p)).target := by
    apply (realTransportChart_target (phaseDuplicate p) _).mpr
    rw [realPhaseChart_eq_extChartAt p p (mem_chart_source _ _)]
    exact mem_extChartAt_target p.proj
  have hi := contMDiffWithinAt_extChartAt_symm_range
    (I := realTransportModel n) (n := ∞) (phaseDuplicate p) hz
  rw [ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ] at hi
  have hm : ContMDiff 𝓘(ℝ, ComplexVector n × ComplexVector n)
      𝓘(ℝ, ComplexVector n × (ComplexVector n × ComplexVector n)) ∞ (phaseDuplicateCLM n) :=
    (phaseDuplicateCLM n).contDiff.contMDiff
  have hp : ContMDiffAt (realPhaseModel n) 𝓘(ℝ, ComplexVector n × ComplexVector n) ∞
      (extChartAt (realPhaseModel n) p) p := contMDiffAt_extChartAt
  exact (hi.comp p ((hm _).comp p hp)).congr_of_eventuallyEq (phaseDuplicate_eventually_chart p)

theorem mfderiv_phaseDuplicate (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := manifold_realTransport M
    mfderiv (realPhaseModel n) (realTransportModel n) phaseDuplicate p = phaseDuplicateCLM n := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := manifold_realTransport M
  letI := realPhaseModel_boundaryless n
  have hf := (phaseDuplicate_smooth (M := M) p).mdifferentiableAt (by simp)
  have heq : writtenInExtChartAt (realPhaseModel n) (realTransportModel n) p phaseDuplicate
      =ᶠ[𝓝 (extChartAt (realPhaseModel n) p p)] phaseDuplicateCLM n := by
    filter_upwards [(isOpen_extChartAt_target (I := realPhaseModel n) p).mem_nhds
      (mem_extChartAt_target p)] with q hq
    have hz := (realPhaseChart_target p q).mp hq
    have hz' : (phaseDuplicateCLM n q).1 ∈ chartTarget p.proj := hz
    have hs : (realTransportPoint p.proj (phaseDuplicateCLM n q)).proj ∈
        (chartAt (ComplexVector n) p.proj).source := by
      simpa only [realTransportPoint, extChartAt_source, chartInv] using
        (extChartAt (ComplexModel n) p.proj).map_target hz'
    change extChartAt (realTransportModel n) (phaseDuplicate p)
      (phaseDuplicate ((extChartAt (realPhaseModel n) p).symm q)) = phaseDuplicateCLM n q
    rw [realPhasePoint_eq_extChartAt_symm p q hz, phaseDuplicate_realPhasePoint,
      realTransportChart_eq_extChartAt (phaseDuplicate p) _ hs]
    exact realTransportChart_realTransportPoint p.proj _ hz'
  rw [hf.mfderiv_abuse, ModelWithCorners.range_eq_univ, fderivWithin_univ,
    heq.fderiv_eq, (phaseDuplicateCLM n).hasFDerivAt.fderiv]

end Yau.Blueprint.C02Proof

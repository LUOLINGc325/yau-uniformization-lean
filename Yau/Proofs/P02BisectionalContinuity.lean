import Yau.Proofs.P02BisectionalNaturality

noncomputable section
open Filter
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.P02Aux
open Yau Yau.LeafProofs L12Aux L23Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem coordinateRm_continuousAt_comp {E : Type*} [TopologicalSpace E]
    (h : HermitianField M) (hs : MetricSmooth h) (c : M.Carrier)
    (z U V W T : E → ComplexVector n) (a : E)
    (hz : ContinuousAt z a) (hU : ContinuousAt U a) (hV : ContinuousAt V a)
    (hW : ContinuousAt W a) (hT : ContinuousAt T a) (ha : z a ∈ chartTarget c) :
    ContinuousAt (fun p => coordinateRm h c (z p) (U p) (V p) (W p) (T p)) a := by
  unfold coordinateRm
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  apply tendsto_finsetSum
  intro k _
  apply tendsto_finsetSum
  intro l _
  have hcoef : ContinuousAt (fun p => curvature4 h c (z p) i j k l) a :=
    ((rmTensor_contDiffOn h hs c ![i,j,k,l]).continuousOn.continuousAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds ha)).comp hz
  simpa only [ContinuousAt, Pi.mul_def, Pi.mul_apply, Function.comp_def, realCoordCLM_apply] using
    (((hcoef.mul ((realCoordCLM i).continuous.continuousAt.comp hU)).mul
    ((realCoordCLM j).continuous.continuousAt.comp hV)).mul
    ((realCoordCLM k).continuous.continuousAt.comp hW)).mul
    ((realCoordCLM l).continuous.continuousAt.comp hT)

theorem coordinateBisectional_continuousAt_comp {E : Type*} [TopologicalSpace E]
    (h : HermitianField M) (hs : MetricSmooth h) (c : M.Carrier)
    (z U V : E → ComplexVector n) (a : E)
    (hz : ContinuousAt z a) (hU : ContinuousAt U a) (hV : ContinuousAt V a)
    (ha : z a ∈ chartTarget c) :
    ContinuousAt (fun p => coordinateBisectional h c (z p) (U p) (V p)) a := by
  exact (coordinateRm_continuousAt_comp h hs c z U V V U a hz hU hV hV hU ha).add
    (coordinateRm_continuousAt_comp h hs c z U (fun p => Complex.I • V p)
      (fun p => Complex.I • V p) U a hz hU (hV.const_smul Complex.I)
      (hV.const_smul Complex.I) hU ha)

theorem transportBisectional_continuous (h : HermitianField M) (hs : MetricSmooth h) :
    letI := manifold_realSmooth M
    Continuous (transportBisectional h) := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  apply continuous_iff_continuousAt.mpr
  intro q
  have hsrc : ∀ᶠ p in 𝓝 q,
      p.proj ∈ (chartAt (ComplexVector n) q.proj).source := by
    filter_upwards [extChartAt_source_mem_nhds (I := realTransportModel n) q] with p hp
    exact (realTransportChart_source q p).mp hp
  have hchart : ContinuousAt (realTransportChart q.proj) q := by
    apply (continuousAt_extChartAt (I := realTransportModel n) q).congr_of_eventuallyEq
    filter_upwards [hsrc] with p hp
    exact (realTransportChart_eq_extChartAt q p hp).symm
  have hz : chartPt q.proj q.proj ∈ chartTarget q.proj := mem_extChartAt_target _
  have HC := coordinateBisectional_continuousAt_comp h hs q.proj
    (fun p : realTransportBundle M => (realTransportChart q.proj p).1)
    (fun p => (realTransportChart q.proj p).2.1)
    (fun p => (realTransportChart q.proj p).2.2) q
    hchart.fst hchart.snd.fst hchart.snd.snd hz
  apply HC.congr_of_eventuallyEq
  filter_upwards [hsrc] with p hp
  exact transportBisectional_in_chart h hs q.proj p hp

end Yau.NodeProofs.P02Aux

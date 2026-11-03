import Yau.LeafProofs.L23DistanceEnergyTraceBound

/-! Genuine parallel transport carries complete endpoint frames into the second-variation trace. -/

noncomputable section
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

variable {n : ℕ} {M : ComplexManifold n}

theorem realFrameEquiv_symm_eq_realTangentCoords (x : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    (realFrameEquiv x).symm v=realTangentCoords x x v := by
  apply (realFrameEquiv x).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  have H : realFrameEquiv x (realTangentCoords x x v)=v := by
    change (realFrameEquiv x).toContinuousLinearMap (realTangentCoords x x v)=v
    rw [realFrameEquiv_toContinuousLinearMap,realFrameCLM_realTangentCoords x x (mem_chart_source _ _)]
  exact H.symm

theorem parallelSecondDensity_trace_le
    (h : HermitianField M) (hh : MetricSmooth h) (y x : M.Carrier)
    (P : ComplexVector n ≃L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) x)
    (hP : ∀ v w : ComplexVector n,
      (underlyingRealRiemannianMetric h).inner x (P v) (P w)=realMetricInChart h y (chartPt y y) v w)
    (T : ComplexVector n) (u K d : ℝ) (hK : curvatureJetNorm h 0 x≤K)
    (hspeed : realMetricInChart h x (chartPt x x) T T=d^2)
    (b : letI := underlyingRealTangentNormedAddCommGroup h y
      letI := underlyingRealTangentInnerProductSpace h y
      OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y))
    (D : Fin (2*n) → ℝ)
    (hD : ∀ i, let V := realTangentCoords x x (P (realTangentCoords y y (b i)))
      D i=2*realMetricInChart h x (chartPt x x) V V+
        2*realMetricInChart h x (chartPt x x) T
          (connectionCurvature (chartChristoffelBilin h x) (chartPt x x) (u • V) T (u • V))) :
    (∑ i, D i)≤2*(2*n : ℕ)+2*u^2*(2*n : ℕ)*K*d^2 := by
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup h z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace h z
  let Q := fieldFrameTransportIsometry h y x P hP
  let b' := b.map Q
  have hB (i : Fin (2*n)) : b' i=P (realTangentCoords y y (b i)) := by
    change P ((realFrameEquiv y).symm (b i))=P (realTangentCoords y y (b i))
    rw [realFrameEquiv_symm_eq_realTangentCoords]
  have H := secondEnergyDensity_orthonormal_trace_le h hh x T u K d hK hspeed b'
  refine le_trans (le_of_eq ?_) H
  apply Finset.sum_congr rfl
  intro i _
  simpa only [hB] using hD i

end Yau.LeafProofs.L23Aux

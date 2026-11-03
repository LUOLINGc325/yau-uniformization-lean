import Yau.LeafProofs.L23DistanceEnergyTrace
import Yau.LeafProofs.L23FieldMetricFrameEquiv

/-! Actual complete orthonormal endpoint frames and their genuine parallel images. -/

noncomputable section
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable {n : ℕ} {M : ComplexManifold n}

def fieldOrthonormalFrame (h : HermitianField M) (x : M.Carrier) :
    letI := underlyingRealTangentNormedAddCommGroup h x
    letI := underlyingRealTangentInnerProductSpace h x
    OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x) := by
  letI := underlyingRealTangentNormedAddCommGroup h x
  letI := underlyingRealTangentInnerProductSpace h x
  exact (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x)).reindex
    (finCongr (realTangent_finrank x))

def fieldFrameTransportIsometry (h : HermitianField M) (y x : M.Carrier)
    (P : ComplexVector n ≃L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) x)
    (hP : ∀ v w : ComplexVector n,
      (underlyingRealRiemannianMetric h).inner x (P v) (P w)=
        realMetricInChart h y (chartPt y y) v w) :
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup h z
    letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentInnerProductSpace h z
    TangentSpace 𝓘(ℝ, ComplexVector n) y ≃ₗᵢ[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) x := by
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup h z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace h z
  let Q := (realFrameEquiv y).toLinearEquiv.symm.trans P.toLinearEquiv
  refine ⟨Q,?_⟩
  intro v
  have H := hP ((realFrameEquiv y).symm v) ((realFrameEquiv y).symm v)
  have Hv : realFrameCLM y y ((realFrameEquiv y).symm v)=v := by
    rw [←realFrameEquiv_toContinuousLinearMap]
    exact (realFrameEquiv y).apply_symm_apply v
  have HG : realMetricInChart h y (chartPt y y) ((realFrameEquiv y).symm v)
      ((realFrameEquiv y).symm v)=inner ℝ v v := by
    rw [realMetricInChart_self_frame,Hv]
    rfl
  rw [HG] at H
  change inner ℝ (Q v) (Q v)=inner ℝ v v at H
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at H
  nlinarith [norm_nonneg (Q v),norm_nonneg v]

end Yau.LeafProofs.L23Aux

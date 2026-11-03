import Yau.LeafProofs.L23DistanceEnergyCurvature

/-! Multilinearity and the full actual curvature contraction in arbitrary directions. -/

noncomputable section
open scoped Topology ContDiff
namespace Yau.LeafProofs.L23Aux
open L12Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def connectionCurvatureMap (Γ : V → V →L[ℝ] V →L[ℝ] V) (z : V) :
    V →L[ℝ] V →L[ℝ] V →L[ℝ] V :=
  let D := fderiv ℝ Γ z
  let B := (ContinuousLinearMap.compL ℝ V V V).bilinearComp (Γ z) (Γ z)
  D-D.flip+B-B.flip

theorem connectionCurvatureMap_apply (Γ : V → V →L[ℝ] V →L[ℝ] V) (z u v w : V) :
    connectionCurvatureMap Γ z u v w=connectionCurvature Γ z u v w := rfl

variable {n : ℕ} {M : ComplexManifold n}

theorem connectionCurvature_eq_sum (Γ : ComplexVector n → ComplexVector n →L[ℝ]
    ComplexVector n →L[ℝ] ComplexVector n) (z u v w : ComplexVector n) :
    connectionCurvature Γ z u v w=∑ i, ∑ j, ∑ k,
      (realCoord u i*realCoord v j*realCoord w k) •
        connectionCurvature Γ z (realVec i) (realVec j) (realVec k) := by
  simp only [←connectionCurvatureMap_apply]
  conv_lhs => rw [←sum_realCoord_realVec u,←sum_realCoord_realVec v,←sum_realCoord_realVec w]
  simp only [map_sum,sum_apply,map_smul,smul_apply,Finset.smul_sum,smul_smul,mul_assoc]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  ring

theorem connectionCurvature_pair_eq_sum (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z∈chartTarget c) (u v w T : ComplexVector n) :
    realMetricInChart h c z (connectionCurvature (chartChristoffelBilin h c) z u v w) T=
      ∑ i, ∑ j, ∑ k, ∑ l,
        (realCoord u i*realCoord v j*realCoord w k*realCoord T l)*rmTensor h c z ![i,j,k,l] := by
  have hb (i j k : RIdx n) : realMetricInChart h c z
      (connectionCurvature (chartChristoffelBilin h c) z (realVec i) (realVec j) (realVec k)) T=
        ∑ l, realCoord T l*rmTensor h c z ![i,j,k,l] := by
    conv_lhs => rw [←sum_realCoord_realVec T]
    simp only [map_sum,map_smul,smul_eq_mul,connectionCurvature_pair_basis h hh c hz]
  rw [connectionCurvature_eq_sum]
  simp only [map_sum,sum_apply,map_smul,smul_apply,smul_eq_mul,hb,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

end Yau.LeafProofs.L23Aux

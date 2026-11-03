import Yau.LeafProofs.L17BootstrapScalarCorrectionBasic

/-! Exact cancellation of the actual normalized partition in the scalar assembly. -/
noncomputable section
open Set Metric
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace Yau.LeafProofs.L17BootstrapScalarCorrectionAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPatchAux
open L17LocalHolderAlgebraAux L17LocalScalarAssemblyAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} (D : BootstrapPatch P x)
variable {T gamma : ℝ}

/-- The true weighted finsum equals the dependent selected-chart zero extension. -/
theorem scalarAssemblyFunction_mul_eq_patch (d sigma : LocalHolderSpace ℝ P T gamma)
    (hd : ∀ q : LocalCylinder P T,
      q.1 ≠ D.center ∨ (q.2.1 : ComplexVector n) ∉ tsupport D.bump → localFun ℝ d q = 0)
    (hsigma : ∀ q : LocalCylinder P T, localFun ℝ sigma q =
      if q.1 = D.center then chartWeightSum P.charts P.centers P.radius P.radius_pos
        (P.charts.chart D.center q.2.1) else 0)
    (hcancel : ∀ z ∈ tsupport D.bump,
      P.weight D.center (P.charts.chart D.center z) *
        chartWeightSum P.charts P.centers P.radius P.radius_pos (P.charts.chart D.center z) = 1) :
    scalarAssemblyFunction P (localBilinearCLM (ContinuousLinearMap.mul ℝ ℝ) sigma d) =
      patchScalarValue D d := by
  classical
  funext q
  have hSingle : scalarAssemblyFunction P
      (localBilinearCLM (ContinuousLinearMap.mul ℝ ℝ) sigma d) q =
      scalarAssemblyTerm P (localBilinearCLM (ContinuousLinearMap.mul ℝ ℝ) sigma d) D.center q :=
    finsum_eq_single _ D.center (fun p hp => scalarAssemblyTerm_mul_zero D d sigma hd p hp q)
  rw [hSingle]
  unfold scalarAssemblyTerm patchScalarValue
  split_ifs with hy hz
  · let a : LocalCylinder P T :=
      ⟨D.center,(⟨(P.charts.chart D.center).symm q.1,hz⟩,q.2)⟩
    rw [localBilinearCLM_value]
    change P.weight D.center q.1 * (localFun ℝ sigma a * localFun ℝ d a) = localFun ℝ d a
    have hs : localFun ℝ sigma a = chartWeightSum P.charts P.centers P.radius P.radius_pos
        (P.charts.chart D.center ((P.charts.chart D.center).symm q.1)) := by
      simpa [a] using hsigma a
    rw [hs,(P.charts.chart D.center).right_inv hy]
    by_cases hSupport : (P.charts.chart D.center).symm q.1 ∈ tsupport D.bump
    · have hc := hcancel ((P.charts.chart D.center).symm q.1) hSupport
      rw [(P.charts.chart D.center).right_inv hy] at hc
      calc
        _ = (P.weight D.center q.1 *
            chartWeightSum P.charts P.centers P.radius P.radius_pos q.1) * localFun ℝ d a := by ring
        _ = localFun ℝ d a := by rw [hc,one_mul]
    · rw [hd a (Or.inr hSupport),mul_zero,mul_zero]
  · rfl
  · rfl

/-- A genuine scalar assembly CLM therefore has the exact selected-chart value. -/
theorem scalarCorrection_holderFun (J : LocalHolderSpace ℝ P T gamma →L[ℝ] HolderSpace P T gamma)
    (hJ : ∀ u, holderFun (J u) = scalarAssemblyFunction P u)
    (d sigma : LocalHolderSpace ℝ P T gamma)
    (hd : ∀ q : LocalCylinder P T,
      q.1 ≠ D.center ∨ (q.2.1 : ComplexVector n) ∉ tsupport D.bump → localFun ℝ d q = 0)
    (hsigma : ∀ q : LocalCylinder P T, localFun ℝ sigma q =
      if q.1 = D.center then chartWeightSum P.charts P.centers P.radius P.radius_pos
        (P.charts.chart D.center q.2.1) else 0)
    (hcancel : ∀ z ∈ tsupport D.bump,
      P.weight D.center (P.charts.chart D.center z) *
        chartWeightSum P.charts P.centers P.radius P.radius_pos (P.charts.chart D.center z) = 1) :
    holderFun (J (localBilinearCLM (ContinuousLinearMap.mul ℝ ℝ) sigma d)) = patchScalarValue D d :=
  (hJ _).trans (scalarAssemblyFunction_mul_eq_patch D d sigma hd hsigma hcancel)

/-- Continuity of the extension follows from the actual assembly, rather than being an input. -/
theorem patchScalarValue_continuous (J : LocalHolderSpace ℝ P T gamma →L[ℝ] HolderSpace P T gamma)
    (hJ : ∀ u, holderFun (J u) = scalarAssemblyFunction P u)
    (d sigma : LocalHolderSpace ℝ P T gamma)
    (hd : ∀ q : LocalCylinder P T,
      q.1 ≠ D.center ∨ (q.2.1 : ComplexVector n) ∉ tsupport D.bump → localFun ℝ d q = 0)
    (hsigma : ∀ q : LocalCylinder P T, localFun ℝ sigma q =
      if q.1 = D.center then chartWeightSum P.charts P.centers P.radius P.radius_pos
        (P.charts.chart D.center q.2.1) else 0)
    (hcancel : ∀ z ∈ tsupport D.bump,
      P.weight D.center (P.charts.chart D.center z) *
        chartWeightSum P.charts P.centers P.radius P.radius_pos (P.charts.chart D.center z) = 1) :
    Continuous (patchScalarValue D d) := by
  rw [← scalarCorrection_holderFun D J hJ d sigma hd hsigma hcancel]
  exact (J (localBilinearCLM (ContinuousLinearMap.mul ℝ ℝ) sigma d)).val.1.continuous

end Yau.LeafProofs.L17BootstrapScalarCorrectionAux

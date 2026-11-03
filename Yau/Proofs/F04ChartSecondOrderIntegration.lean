import Yau.Proofs.F04DiffusionIntegrationByParts

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
namespace Yau.F04Proof
open Yau.LeafProofs.L18Aux

/-- A single genuine Hessian entry, tested against the actual variable
 coefficient, gives both its gradient flux and its coefficient drift. -/
theorem integral_chart_coefficient_hessian
    {n : ℕ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    {η A v : ComplexVector n → ℝ}
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) (hηO : tsupport η ⊆ O)
    (hA : ContDiffOn ℝ 1 A O) (hv : ContDiffOn ℝ 2 v O) (i j : RIdx n) :
    (∫ z in O, η z * A z * fderiv ℝ (fderiv ℝ v) z (realVec i) (realVec j)) =
      -(∫ z in O, rDeriv v z j * (A z * rDeriv η z i + rDeriv A z i * η z)) := by
  have hD : ContDiffOn ℝ 1 (fun z => rDeriv v z j) O :=
    (hv.fderiv_of_isOpen hO (by norm_num)).clm_apply contDiffOn_const
  have hIP := integral_compactTest_coefficient_direction_on volume hO hη hcη hηO hA hD (realVec i)
  change (∫ z in O, η z * A z * rDeriv (fun w => rDeriv v w j) z i) =
    -(∫ z in O, rDeriv v z j * (A z * rDeriv η z i + rDeriv A z i * η z)) at hIP
  calc
    _ = ∫ z in O, η z * A z * rDeriv (fun w => rDeriv v w j) z i := by
      apply setIntegral_congr_fun hO.measurableSet
      intro z hz
      change η z * A z * fderiv ℝ (fderiv ℝ v) z (realVec i) (realVec j) =
        η z * A z * rDeriv (fun w => rDeriv v w j) z i
      rw [rDeriv_rDeriv_eq_hessian (hv.contDiffAt (hO.mem_nhds hz)) i j]
    _ = _ := hIP

end Yau.F04Proof

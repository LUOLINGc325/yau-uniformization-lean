import Yau.Proofs.F05BootstrapIntegralCalculus

/-! The fundamental theorem on a genuine closed time interval keeps both
endpoint derivatives within that interval. -/

open Set Filter MeasureTheory
open scoped Topology Interval
noncomputable section
namespace Yau.Proofs.F05Aux
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem F05_closed_primitive_derivative {l r : ℝ} {F : ℝ → V}
    (hF : ContinuousOn F (Icc l r)) {t : ℝ} (ht : t ∈ Icc l r) :
    HasDerivWithinAt (fun q => ∫ a in l..q, F a) (F t) (Icc l r) t := by
  letI : Fact (t ∈ Icc l r) := ⟨ht⟩
  have hSub : uIcc l t ⊆ Icc l r := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc_right ht.2
  exact intervalIntegral.integral_hasDerivWithinAt_right
    (hF.mono hSub).intervalIntegrable
    (hF.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hF t ht)

end Yau.Proofs.F05Aux

import Yau.LeafProofs.L23FieldMetricParallelInterval

/-! Matrix parallel transport obeys the genuine connection change law. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 800000

theorem parallel_matrix_change_hasDerivAt
    (h : HermitianField M) (hh : MetricSmooth h) (a b : M.Carrier)
    {z : ℝ → ComplexVector n} {W : ℝ → ComplexVector n →L[ℝ] ComplexVector n}
    {t : ℝ} {T : ComplexVector n}
    (hz : z t ∈ chartTarget a) (hb : chartInv a (z t) ∈ (extChartAt (ComplexModel n) b).source)
    (hzt : HasDerivAt z T t)
    (hW : HasDerivAt W ((-chartChristoffelBilin h a (z t) T).comp (W t)) t) :
    HasDerivAt (fun u => (fderiv ℝ (realChartChange a b) (z u)).comp (W u))
      ((-chartChristoffelBilin h b (realChartChange a b (z t))
        (fderiv ℝ (realChartChange a b) (z t) T)).comp
          ((fderiv ℝ (realChartChange a b) (z t)).comp (W t))) t := by
  have Hψ := realChartChange_contDiffAt a b hz hb
  have HD : ContDiffAt ℝ ∞ (fderiv ℝ (realChartChange a b)) (z t) := Hψ.fderiv_right (by simp)
  have Hcoef := (HD.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hzt
  let V : ℝ → ComplexVector n →L[ℝ] ComplexVector n :=
    fun u => (fderiv ℝ (realChartChange a b) (z u)).comp (W u)
  let D : ComplexVector n →L[ℝ] ComplexVector n :=
    (fderiv ℝ (fderiv ℝ (realChartChange a b)) (z t) T).comp (W t)+
      (fderiv ℝ (realChartChange a b) (z t)).comp ((-chartChristoffelBilin h a (z t) T).comp (W t))
  have HM : HasDerivAt V D t := Hcoef.clm_comp hW
  convert! HM using 1
  apply ContinuousLinearMap.ext
  intro v
  have HWv : HasDerivAt (fun u => W u v) (-chartChristoffelBilin h a (z t) T (W t v)) t := by
    convert! hW.clm_apply (hasDerivAt_const t v) using 1 <;>
      simp only [map_zero,add_zero,ContinuousLinearMap.comp_apply,ContinuousLinearMap.neg_apply]
  have HX := parallel_vector_change_hasDerivAt h hh a b hz hb hzt HWv
  have HY : HasDerivAt (fun u => V u v) (D v) t := by
    simpa only [map_zero,add_zero] using HM.clm_apply (hasDerivAt_const t v)
  exact HX.unique HY

end Yau.LeafProofs.L23Aux

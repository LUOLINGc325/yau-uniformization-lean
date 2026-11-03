import Yau.LeafProofs.L23FieldMetricFirstVariation
import Yau.LeafProofs.L23FieldMetricLinearODEGlobal

/-! The actual weak connection along a C3 curve and its parallel-vector calculus. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 800000

theorem chartChristoffelBilin_contDiffOn (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier) :
    ContDiffOn ℝ ∞ (chartChristoffelBilin h c) (chartTarget c) := by
  apply contDiffOn_clm_apply.mpr
  intro u
  apply contDiffOn_clm_apply.mpr
  intro v
  simp only [chartChristoffelBilin_apply]
  apply ContDiffOn.sum
  intro k _
  apply ContDiffOn.smul_const
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro j _
  exact ((christoffel_contDiffOn h hh c k i j).mul contDiffOn_const).mul contDiffOn_const

theorem curve_coordinates_contDiffOn_three
    (γ : ℝ → M.Carrier) (c : M.Carrier) (J : Set ℝ) (hJ : IsOpen J) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 γ J →
    Set.MapsTo γ J (chartAt (ComplexVector n) c).source →
    ContDiffOn ℝ 3 (fun t => chartPt c (γ t)) J := by
  letI := manifold_realSmooth M
  intro hγ hsource t ht
  have HC : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 3 (chartPt c) (γ t) := by
    convert! (contMDiffAt_extChartAt' (I := 𝓘(ℝ, ComplexVector n)) (n := 3)
      (x := c) (x' := γ t) (hsource ht)) using 1
  exact (HC.comp t ((hγ t ht).contMDiffAt (hJ.mem_nhds ht))).contDiffAt.contDiffWithinAt

def chartParallelCoefficient (h : HermitianField M) (c : M.Carrier) (γ : ℝ → M.Carrier) (t : ℝ) :
    ComplexVector n →L[ℝ] ComplexVector n :=
  -chartChristoffelBilin h c (chartPt c (γ t)) (deriv (fun u => chartPt c (γ u)) t)

theorem chartParallelCoefficient_contDiffOn_two
    (h : HermitianField M) (hh : MetricSmooth h) (γ : ℝ → M.Carrier)
    (c : M.Carrier) (J : Set ℝ) (hJ : IsOpen J) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 γ J →
    Set.MapsTo γ J (chartAt (ComplexVector n) c).source →
    ContDiffOn ℝ 2 (chartParallelCoefficient h c γ) J := by
  letI := manifold_realSmooth M
  intro hγ hsource
  have Hcoord := curve_coordinates_contDiffOn_three γ c J hJ hγ hsource
  have HΓ : ContDiffOn ℝ 2 (fun t => chartChristoffelBilin h c (chartPt c (γ t))) J :=
    ((chartChristoffelBilin_contDiffOn h hh c).of_le (by simp)).comp (Hcoord.of_le (by norm_num))
      (fun t ht => (extChartAt (ComplexModel n) c).map_source (by simpa only [extChartAt_source] using hsource ht))
  exact (HΓ.clm_apply (Hcoord.deriv_of_isOpen hJ (by norm_num))).neg

theorem parallel_vector_change_hasDerivAt
    (h : HermitianField M) (hh : MetricSmooth h) (a b : M.Carrier)
    {z w : ℝ → ComplexVector n} {t : ℝ} {T : ComplexVector n}
    (hz : z t ∈ chartTarget a) (hb : chartInv a (z t) ∈ (extChartAt (ComplexModel n) b).source)
    (hzt : HasDerivAt z T t)
    (hw : HasDerivAt w (-chartChristoffelBilin h a (z t) T (w t)) t) :
    HasDerivAt (fun u => fderiv ℝ (realChartChange a b) (z u) (w u))
      (-chartChristoffelBilin h b (realChartChange a b (z t))
        (fderiv ℝ (realChartChange a b) (z t) T)
        (fderiv ℝ (realChartChange a b) (z t) (w t))) t := by
  have Hψ := realChartChange_contDiffAt a b hz hb
  have HD : ContDiffAt ℝ ∞ (fderiv ℝ (realChartChange a b)) (z t) := Hψ.fderiv_right (by simp)
  have Hcoef := (HD.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hzt
  have H := Hcoef.clm_apply hw
  convert! H using 1
  simp only [Function.comp_apply,map_neg]
  rw [chartChristoffelBilin_change h hh a b hz hb T (w t)]
  abel

theorem realMetricInChart_parallelPair_hasDerivAt
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    {z a b : ℝ → ComplexVector n} {t : ℝ} {T : ComplexVector n}
    (hz : z t ∈ chartTarget c) (hzt : HasDerivAt z T t)
    (ha : HasDerivAt a (-chartChristoffelBilin h c (z t) T (a t)) t)
    (hb : HasDerivAt b (-chartChristoffelBilin h c (z t) T (b t)) t) :
    HasDerivAt (fun u => realMetricInChart h c (z u) (a u) (b u)) 0 t := by
  simpa only [neg_add_cancel,map_zero,ContinuousLinearMap.zero_apply,zero_add] using
    realMetricInChart_pairing_hasDerivAt h hh c hz hzt ha hb

theorem chartParallel_matrix_pairing_constant
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    (z T : ℝ → ComplexVector n) (W : ℝ → ComplexVector n →L[ℝ] ComplexVector n)
    {a b s t : ℝ}
    (hz : ∀ u ∈ Set.Ioo a b, z u ∈ chartTarget c ∧ HasDerivAt z (T u) u)
    (hW : ∀ u ∈ Set.Ioo a b, HasDerivAt W ((-chartChristoffelBilin h c (z u) (T u)).comp (W u)) u)
    (v w : ComplexVector n) (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) :
    realMetricInChart h c (z s) (W s v) (W s w) = realMetricInChart h c (z t) (W t v) (W t w) := by
  have hvec (V : ComplexVector n) (u : ℝ) (hu : u ∈ Set.Ioo a b) :
      HasDerivAt (fun r => W r V) (-chartChristoffelBilin h c (z u) (T u) (W u V)) u := by
    convert! (hW u hu).clm_apply (hasDerivAt_const u V) using 1 <;>
      simp only [map_zero,zero_add,add_zero,ContinuousLinearMap.comp_apply,ContinuousLinearMap.neg_apply]
  have hpair (u : ℝ) (hu : u ∈ Set.Ioo a b) :
      HasDerivAt (fun r => realMetricInChart h c (z r) (W r v) (W r w)) 0 u :=
    realMetricInChart_parallelPair_hasDerivAt h hh c (hz u hu).1 (hz u hu).2 (hvec v u hu) (hvec w u hu)
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun u hu => (hpair u hu).differentiableAt.differentiableWithinAt)
    (fun u hu => (hpair u hu).deriv) hs ht

end Yau.LeafProofs.L23Aux

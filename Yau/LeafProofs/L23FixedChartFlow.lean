import Yau.LeafProofs.L23RicciNaturality
import Yau.LeafProofs.L23MetricTimeCalculus

/-! The original centered Ricci-flow equation in every fixed actual chart. -/

noncomputable section
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem localRealRicciFlow_metric_hasDerivAt_inChart
    (h : ℝ → HermitianField M) (O : Set M.Carrier) (a b σ : ℝ)
    (hflow : LocalRealRicciFlow h O (Set.Icc a b) σ)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hx : chartInv c z ∈ O) (t : ℝ) (ht : t ∈ Set.Ioo a b) (i j : RIdx n) :
    HasDerivAt (fun s => realMetricFn (h s) c z i j)
      (-σ*realRicciCoeff (h t) c z i j) t := by
  let d := chartInv c z
  have hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source := mem_extChartAt_source d
  have heq : (fun s => realMetricFn (h s) c z i j)=
      (fun s => ∑ p, ∑ q, realChartJacobian c d z p i*
        realMetricFn (h s) d (chartPt d d) p q*realChartJacobian c d z q j) := by
    funext s
    exact realMetricFn_chart_change_entry (h s) c d hz hy i j
  rw [heq]
  have hd := HasDerivAt.sum (u := Finset.univ) (fun p _ =>
    HasDerivAt.sum (u := Finset.univ) (fun q _ =>
      ((localRealRicciFlow_metric_hasDerivAt h O a b σ hflow d hx t ht p q).const_mul
        (realChartJacobian c d z p i)).mul_const (realChartJacobian c d z q j)))
  convert hd using 1
  · funext s
    simp only [Finset.sum_apply]
  · have hh := metricFamilySmooth_slice h hflow.1 ⟨ht.1.le,ht.2.le⟩
    rw [realRicciCoeff_chart_change (h t) hh c d hz hy]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    dsimp only [L12Aux.realChartChange,d]
    ring

theorem localRealRicciFlow_inverseMetric_hasDerivAt_inChart
    (h : ℝ → HermitianField M) (O : Set M.Carrier) (a b σ : ℝ)
    (hflow : LocalRealRicciFlow h O (Set.Icc a b) σ)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hx : chartInv c z ∈ O) (t : ℝ) (ht : t ∈ Set.Ioo a b) (i j : RIdx n) :
    HasDerivAt (fun s => (realMetricFn (h s) c z)⁻¹ i j)
      (σ*∑ p, ∑ q, (realMetricFn (h t) c z)⁻¹ i p*
        realRicciCoeff (h t) c z p q*(realMetricFn (h t) c z)⁻¹ q j) t := by
  have hd := matrixInverse_hasDerivAt (fun s => realMetricFn (h s) c z)
    (fun p q => -σ*realRicciCoeff (h t) c z p q) t
    (localRealRicciFlow_metric_hasDerivAt_inChart h O a b σ hflow c hz hx t ht)
    (L12Aux.realMetricFn_posDef (h t) c z hz).det_pos.ne' i j
  convert hd using 1
  simp only [Matrix.mul_apply,Matrix.neg_apply,Finset.mul_sum,Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

end Yau.LeafProofs.L23Aux

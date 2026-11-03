import Yau.LeafProofs.L23CurvatureTime
import Yau.LeafProofs.L23ConnectionTensorLowering
import Yau.LeafProofs.L23TensorLocalAlgebra

/-! The lowered time variation of the original curvature tensor. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem dotChristoffel_contDiffOn
    (h : ℝ → HermitianField M) (a b : ℝ) (hh : MetricFamilySmooth h (Set.Icc a b))
    (c : M.Carrier) (t : ℝ) (ht : t ∈ Set.Ioo a b) (p i j : RIdx n) :
    ContDiffOn ℝ ∞ (fun z => dotChristoffel h c z t p i j) (chartTarget c) := by
  have hs := joint_time_derivative_contDiffOn
    (fun u : ComplexVector n × ℝ => christoffel (h u.2) c u.1 p i j)
    (flowChartDomain c a b) (isOpen_flowChartDomain c a b)
    (christoffelFamilySmooth_joint h a b hh c p i j)
  have hmap : ContDiffOn ℝ ∞ (fun z : ComplexVector n => (z,t)) (chartTarget c) :=
    contDiffOn_id.prodMk contDiffOn_const
  have hc := hs.comp hmap (fun _ hz => ⟨hz,ht⟩)
  simpa only [Function.comp_def,dotChristoffel] using hc

theorem localRealRicciFlow_lowerConnectionTensor_eq
    (h : ℝ → HermitianField M) (O : Set M.Carrier) (a b σ : ℝ) (hO : IsOpen O)
    (hflow : LocalRealRicciFlow h O (Set.Icc a b) σ)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hx : chartInv c z ∈ O) (t : ℝ) (ht : t ∈ Set.Ioo a b) :
    lowerConnectionTensor (h t) c (fun w => dotChristoffel h c w t) z=
      (fun v : Fin 3 → RIdx n => -(σ/2)*
        (covariantD (h t) c (ricciTensor (h t) c) z ![v 0,v 1,v 2]+
          covariantD (h t) c (ricciTensor (h t) c) z ![v 1,v 0,v 2]-
            covariantD (h t) c (ricciTensor (h t) c) z ![v 2,v 0,v 1])) := by
  funext v
  have hl := localRealRicciFlow_loweredChristoffel_time h O a b σ hO
    hflow c hz hx t ht (v 0) (v 1) (v 2)
  calc
    _=∑ p, deriv (fun s => christoffel (h s) c z p (v 0) (v 1)) t*
        realMetricFn (h t) c z p (v 2) := by
      apply Finset.sum_congr rfl
      intro p _
      change realMetricFn (h t) c z p (v 2)*
        deriv (fun s => christoffel (h s) c z p (v 0) (v 1)) t=_
      ring
    _=_ := hl

theorem localRealRicciFlow_rmTensor_hasDerivAt_lowered
    (h : ℝ → HermitianField M) (O : Set M.Carrier) (a b σ : ℝ)
    (hflow : LocalRealRicciFlow h O (Set.Icc a b) σ)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hx : chartInv c z ∈ O) (t : ℝ) (ht : t ∈ Set.Ioo a b) (i j k l : RIdx n) :
    HasDerivAt (fun s => rmTensor (h s) c z ![i,j,k,l])
      (-σ*(∑ p, realRicciCoeff (h t) c z p l*riemannCoeff (h t) c z i j k p)+
        covariantD (h t) c (lowerConnectionTensor (h t) c
          (fun w => dotChristoffel h c w t)) z ![i,j,k,l]-
          covariantD (h t) c (lowerConnectionTensor (h t) c
            (fun w => dotChristoffel h c w t)) z ![j,i,k,l]) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun p _ =>
    (localRealRicciFlow_metric_hasDerivAt_inChart h O a b σ hflow c hz hx t ht p l).mul
      (riemannCoeff_time_hasDerivAt h a b hflow.1 c hz t ht i j k p))
  have hh := metricFamilySmooth_slice h hflow.1 ⟨ht.1.le,ht.2.le⟩
  have hCd (p j k : RIdx n) := ((dotChristoffel_contDiffOn h a b hflow.1 c t ht p j k).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hcurl := covariantD_lowerConnectionTensor_curl (h t) hh c
    (fun w => dotChristoffel h c w t) hz hCd i j k l
  convert hd using 1
  · funext s
    rfl
  · rw [add_sub_assoc,hcurl]
    simp only [Finset.sum_add_distrib,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    ring

end Yau.LeafProofs.L23Aux

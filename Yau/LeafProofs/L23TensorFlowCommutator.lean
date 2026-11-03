import Yau.LeafProofs.L23RoughLapCommutatorExpanded
import Yau.LeafProofs.L23TensorTimeCommutator

/-! The actual parabolic operator commuted with the original all-slot
covariant derivative, prior to the Ricci-flow cancellations. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {M : ComplexManifold n}

theorem tensorFamilySmooth_slice (c : M.Carrier) (a b : ℝ)
    (A : ℝ → ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => A p.2 p.1 v)
      (flowChartDomain c a b)) (t : ℝ) (ht : t ∈ Set.Ioo a b) (v : Fin r → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => A t z v) (chartTarget c) :=
  (hA v).comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hz => ⟨hz,ht⟩)

theorem tensorFamilySmooth_timeDerivative_slice (c : M.Carrier) (a b : ℝ)
    (A : ℝ → ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => A p.2 p.1 v)
      (flowChartDomain c a b)) (t : ℝ) (ht : t ∈ Set.Ioo a b) (v : Fin r → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => tensorTimeDerivative A t z v) (chartTarget c) := by
  have hs := joint_time_derivative_contDiffOn (fun p : ComplexVector n × ℝ => A p.2 p.1 v)
    (flowChartDomain c a b) (isOpen_flowChartDomain c a b) (hA v)
  have hmap : ContDiffOn ℝ ∞ (fun z : ComplexVector n => (z,t)) (chartTarget c) :=
    contDiffOn_id.prodMk contDiffOn_const
  exact hs.comp hmap (fun _ hz => ⟨hz,ht⟩)

theorem roughLap_contDiffOn (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun w => A w v) (chartTarget c)) (v : Fin r → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => roughLap h c A z v) (chartTarget c) := by
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro j _
  exact (realMetricFn_inverse_contDiffOn h hh c i j).mul
    (covariantD_contDiffOn h hh c (covariantD h c A)
      (covariantD_contDiffOn h hh c A hA) (Fin.cons i (Fin.cons j v)))

def tensorFlowOperator (h : ℝ → HermitianField M) (c : M.Carrier)
    (A : ℝ → ComplexVector n → CovTensor n r) (σ t : ℝ) (z : ComplexVector n) : CovTensor n r :=
  fun v => tensorTimeDerivative A t z v-(σ/2)*roughLap (h t) c (A t) z v

theorem tensorFlowOperator_covariantD_raw
    (h : ℝ → HermitianField M) (a b σ : ℝ) (hh : MetricFamilySmooth h (Set.Icc a b))
    (c : M.Carrier) (A : ℝ → ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => A p.2 p.1 v)
      (flowChartDomain c a b))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (t : ℝ) (ht : t ∈ Set.Ioo a b)
    (i : RIdx n) (v : Fin r → RIdx n) :
    tensorFlowOperator h c (fun s => covariantD (h s) c (A s)) σ t z (Fin.cons i v)=
      covariantD (h t) c (tensorFlowOperator h c A σ t) z (Fin.cons i v)+
        (σ/2)*(covariantD (h t) c (roughLap (h t) c (A t)) z (Fin.cons i v)-
          roughLap (h t) c (covariantD (h t) c (A t)) z (Fin.cons i v))-
            ∑ j : Fin r, ∑ p, dotChristoffel h c z t p i (v j)*A t z (Function.update v j p) := by
  have htime := covariantDFamily_hasDerivAt h a b hh c A hA hz t ht i v
  have hs := metricFamilySmooth_slice h hh ⟨ht.1.le,ht.2.le⟩
  have hAs := tensorFamilySmooth_slice c a b A hA t ht
  have hL (u : Fin r → RIdx n) := ((roughLap_contDiffOn (h t) hs c (A t) hAs u).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hT (u : Fin r → RIdx n) := ((tensorFamilySmooth_timeDerivative_slice c a b A hA t ht u).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hLc (u : Fin r → RIdx n) : DifferentiableAt ℝ
      (fun w => (σ/2)*roughLap (h t) c (A t) w u) z := (hL u).const_mul _
  have hPA : covariantD (h t) c (tensorFlowOperator h c A σ t) z=
      covariantD (h t) c (tensorTimeDerivative A t) z-
        (fun u => (σ/2)*covariantD (h t) c (roughLap (h t) c (A t)) z u) := by
    change covariantD (h t) c (fun w => tensorTimeDerivative A t w-
      (fun u => (σ/2)*roughLap (h t) c (A t) w u)) z=_
    rw [covariantD_sub_at (h t) c _ _ z hT hLc,
      covariantD_const_mul_at (h t) c _ z hL]
  have hp := congrFun hPA (Fin.cons i v)
  change deriv (fun s => covariantD (h s) c (A s) z (Fin.cons i v)) t-
    (σ/2)*roughLap (h t) c (covariantD (h t) c (A t)) z (Fin.cons i v)=_
  rw [htime.deriv]
  change covariantD (h t) c (tensorFlowOperator h c A σ t) z (Fin.cons i v)=
    covariantD (h t) c (tensorTimeDerivative A t) z (Fin.cons i v)-
      (σ/2)*covariantD (h t) c (roughLap (h t) c (A t)) z (Fin.cons i v) at hp
  nlinarith [hp]

end Yau.LeafProofs.L23Aux

import Yau.LeafProofs.L23TensorFamilySmooth
import Yau.LeafProofs.L23JointClosedCalculus

/-! Genuine joint regularity on the entire closed flow slab. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

def flowChartClosedDomain (c : M.Carrier) (a b : ℝ) : Set (ComplexVector n × ℝ) :=
  chartTarget c ×ˢ Set.Icc a b

theorem metricFamilySmooth_joint_closed (h : ℝ → HermitianField M) (a b : ℝ)
    (hab : a < b) (hh : MetricFamilySmooth h (Set.Icc a b)) (c : M.Carrier) (i j : RIdx n) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => realMetricFn (h p.2) c p.1 i j)
      (flowChartClosedDomain c a b) :=
  hh c i j

theorem inverseMetricFamilySmooth_joint_closed (h : ℝ → HermitianField M) (a b : ℝ)
    (hab : a < b) (hh : MetricFamilySmooth h (Set.Icc a b)) (c : M.Carrier) (i j : RIdx n) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => (realMetricFn (h p.2) c p.1)⁻¹ i j)
      (flowChartClosedDomain c a b) :=
  L12Aux.contDiffOn_matrix_inv (metricFamilySmooth_joint_closed h a b hab hh c)
    (fun p hp => (L12Aux.realMetricFn_posDef (h p.2) c p.1 hp.1).det_pos.ne') i j

theorem christoffelFamilySmooth_joint_closed (h : ℝ → HermitianField M) (a b : ℝ)
    (hab : a < b) (hh : MetricFamilySmooth h (Set.Icc a b)) (c : M.Carrier) (l i j : RIdx n) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => christoffel (h p.2) c p.1 l i j)
      (flowChartClosedDomain c a b) := by
  apply contDiffOn_const.mul
  apply ContDiffOn.sum
  intro q _
  apply (inverseMetricFamilySmooth_joint_closed h a b hab hh c l q).mul
  exact ((joint_spatial_derivative_contDiffOn_closedInterval _ _
    (isOpen_extChartAt_target (I := ComplexModel n) c) a b hab
    (metricFamilySmooth_joint_closed h a b hab hh c j q) i).add
      (joint_spatial_derivative_contDiffOn_closedInterval _ _
    (isOpen_extChartAt_target (I := ComplexModel n) c) a b hab
        (metricFamilySmooth_joint_closed h a b hab hh c i q) j)).sub
          (joint_spatial_derivative_contDiffOn_closedInterval _ _
    (isOpen_extChartAt_target (I := ComplexModel n) c) a b hab
            (metricFamilySmooth_joint_closed h a b hab hh c i j) q)

theorem riemannCoeffFamilySmooth_joint_closed (h : ℝ → HermitianField M) (a b : ℝ)
    (hab : a < b) (hh : MetricFamilySmooth h (Set.Icc a b)) (c : M.Carrier) (i j k l : RIdx n) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => riemannCoeff (h p.2) c p.1 i j k l)
      (flowChartClosedDomain c a b) := by
  apply ((joint_spatial_derivative_contDiffOn_closedInterval _ _
    (isOpen_extChartAt_target (I := ComplexModel n) c) a b hab
    (christoffelFamilySmooth_joint_closed h a b hab hh c l j k) i).sub
      (joint_spatial_derivative_contDiffOn_closedInterval _ _
    (isOpen_extChartAt_target (I := ComplexModel n) c) a b hab
        (christoffelFamilySmooth_joint_closed h a b hab hh c l i k) j)).add
  apply ContDiffOn.sum
  intro p _
  exact ((christoffelFamilySmooth_joint_closed h a b hab hh c p j k).mul
    (christoffelFamilySmooth_joint_closed h a b hab hh c l i p)).sub
      ((christoffelFamilySmooth_joint_closed h a b hab hh c p i k).mul
        (christoffelFamilySmooth_joint_closed h a b hab hh c l j p))

theorem covariantDFamilySmooth_joint_closed {r : ℕ} (h : ℝ → HermitianField M) (a b : ℝ)
    (hab : a < b) (hh : MetricFamilySmooth h (Set.Icc a b)) (c : M.Carrier)
    (A : ℝ → ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => A p.2 p.1 v)
      (flowChartClosedDomain c a b)) (v : Fin (r+1) → RIdx n) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => covariantD (h p.2) c (A p.2) p.1 v)
      (flowChartClosedDomain c a b) := by
  apply (joint_spatial_derivative_contDiffOn_closedInterval _ _
    (isOpen_extChartAt_target (I := ComplexModel n) c) a b hab
    (hA (fun j => v j.succ)) (v 0)).sub
  apply ContDiffOn.sum
  intro j _
  apply ContDiffOn.sum
  intro q _
  exact (christoffelFamilySmooth_joint_closed h a b hab hh c q (v 0) (v j.succ)).mul
    (hA (Function.update (fun j => v j.succ) j q))

theorem rmTensorFamilySmooth_joint_closed (h : ℝ → HermitianField M) (a b : ℝ)
    (hab : a < b) (hh : MetricFamilySmooth h (Set.Icc a b)) (c : M.Carrier) (v : Fin 4 → RIdx n) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => rmTensor (h p.2) c p.1 v)
      (flowChartClosedDomain c a b) := by
  apply ContDiffOn.sum
  intro l _
  exact (metricFamilySmooth_joint_closed h a b hab hh c l (v 3)).mul
    (riemannCoeffFamilySmooth_joint_closed h a b hab hh c (v 0) (v 1) (v 2) l)

theorem rmJetFamilySmooth_joint_closed (h : ℝ → HermitianField M) (a b : ℝ)
    (hab : a < b) (hh : MetricFamilySmooth h (Set.Icc a b)) (c : M.Carrier) (k : ℕ)
    (v : Fin (4+k) → RIdx n) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => rmJet (h p.2) c k p.1 v)
      (flowChartClosedDomain c a b) := by
  induction k with
  | zero => exact rmTensorFamilySmooth_joint_closed h a b hab hh c v
  | succ k ih =>
      exact covariantDFamilySmooth_joint_closed h a b hab hh c
        (fun t => rmJet (h t) c k) ih v

end Yau.LeafProofs.L23Aux

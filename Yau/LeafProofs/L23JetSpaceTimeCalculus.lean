import Yau.LeafProofs.L23JetScalarCalculus
import Yau.LeafProofs.L23TensorFamilySmooth
import Yau.LeafProofs.L23JetTermCalculus

/-! Actual space-time regularity and reaction sums for scalar jet norms. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {n : ℕ} {M : ComplexManifold n}

theorem chartJetSqFamilySmooth_joint (h : ℝ → HermitianField M) (a b : ℝ)
    (hh : MetricFamilySmooth h (Set.Icc a b)) (c : M.Carrier) (k : ℕ) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ =>
      covTensorNormSq (realMetricFn (h p.2) c p.1) (rmJet (h p.2) c k p.1))
        (flowChartDomain c a b) := by
  apply ContDiffOn.sum
  intro v _
  apply ContDiffOn.sum
  intro w _
  apply ((rmJetFamilySmooth_joint h a b hh c k v).mul
    (rmJetFamilySmooth_joint h a b hh c k w)).mul
  apply contDiffOn_prod
  intro j _
  exact inverseMetricFamilySmooth_joint h a b hh c (v j) (w j)

theorem jetSq_time_contDiffAt (h : ℝ → HermitianField M) (a b : ℝ)
    (hh : MetricFamilySmooth h (Set.Icc a b)) (x : M.Carrier) (k : ℕ)
    (t : ℝ) (ht : t ∈ Set.Ioo a b) : ContDiffAt ℝ ∞ (fun s => jetSq (h s) k x) t := by
  have hJ : ContDiffAt ℝ ∞ (fun p : ComplexVector n × ℝ =>
      covTensorNormSq (realMetricFn (h p.2) x p.1) (rmJet (h p.2) x k p.1)) (chartPt x x,t) :=
    (chartJetSqFamilySmooth_joint h a b hh x k).contDiffAt
      ((isOpen_flowChartDomain x a b).mem_nhds ⟨mem_extChartAt_target x,ht⟩)
  exact hJ.comp t (contDiffAt_const.prodMk contDiffAt_id)

theorem jetSq_joint_contDiffAt (h : ℝ → HermitianField M) (a b : ℝ)
    (hh : MetricFamilySmooth h (Set.Icc a b)) (c : M.Carrier) (k : ℕ)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (t : ℝ) (ht : t ∈ Set.Ioo a b) :
    ContDiffAt ℝ ∞ (fun p : ComplexVector n × ℝ => jetSq (h p.2) k (chartInv c p.1)) (z,t) := by
  have hJ : ContDiffAt ℝ ∞ (fun p : ComplexVector n × ℝ =>
      covTensorNormSq (realMetricFn (h p.2) c p.1) (rmJet (h p.2) c k p.1)) (z,t) :=
    (chartJetSqFamilySmooth_joint h a b hh c k).contDiffAt
    ((isOpen_flowChartDomain c a b).mem_nhds ⟨hz,ht⟩)
  apply hJ.congr_of_eventuallyEq
  filter_upwards [(isOpen_flowChartDomain c a b).mem_nhds (show (z,t) ∈ flowChartDomain c a b from ⟨hz,ht⟩)]
    with p hp
  exact jetSq_inChart (h p.2) (metricFamilySmooth_slice h hh ⟨hp.2.1.le,hp.2.2.le⟩) k c hp.1

def jetReactionSum (h : HermitianField M) (k : ℕ) (x : M.Carrier) : ℝ :=
  ∑ i : Fin (k+1), Real.sqrt (jetSq h i.val x)*Real.sqrt (jetSq h (k-i.val) x)*Real.sqrt (jetSq h k x)

theorem jetReactionSum_nonneg (h : HermitianField M) (k : ℕ) (x : M.Carrier) :
    0 ≤ jetReactionSum h k x :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))

theorem jetConvolution_mul_sqrt (h : HermitianField M) (k : ℕ) (x : M.Carrier) :
    jetConvolution h x k (chartPt x x)*Real.sqrt (jetSq h k x)=jetReactionSum h k x := by
  simp only [jetConvolution,jetReactionSum,jetSq,Finset.sum_mul]

theorem metricReaction_le_jetReactionSum (h : HermitianField M) (k : ℕ) (x : M.Carrier) :
    Real.sqrt (jetSq h 0 x)*jetSq h k x ≤ jetReactionSum h k x := by
  have h0 : Real.sqrt (jetSq h 0 x)*jetSq h k x=
      Real.sqrt (jetSq h 0 x)*Real.sqrt (jetSq h k x)*Real.sqrt (jetSq h k x) := by
    rw [mul_assoc,←pow_two,Real.sq_sqrt (jetSq_nonneg h k x)]
  rw [h0]
  have hs := Finset.single_le_sum (f := fun i : Fin (k+1) =>
    Real.sqrt (jetSq h i.val x)*Real.sqrt (jetSq h (k-i.val) x)*Real.sqrt (jetSq h k x))
    (fun _ _ => mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
    (Finset.mem_univ (0 : Fin (k+1)))
  simpa only [Fin.val_zero, Nat.sub_zero,jetReactionSum] using hs

end Yau.LeafProofs.L23Aux

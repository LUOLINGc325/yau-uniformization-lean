import Yau.LeafProofs.L23TensorFamilyClosedSmooth
import Yau.LeafProofs.L23JetSpaceTimeCalculus

/-! The original curvature jet norms are continuous up to the closed time faces. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem chartJetSqFamilySmooth_joint_closed (h : ℝ → HermitianField M) (a b : ℝ)
    (hab : a < b) (hh : MetricFamilySmooth h (Set.Icc a b)) (c : M.Carrier) (k : ℕ) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ =>
      covTensorNormSq (realMetricFn (h p.2) c p.1) (rmJet (h p.2) c k p.1))
        (flowChartClosedDomain c a b) := by
  apply ContDiffOn.sum
  intro v _
  apply ContDiffOn.sum
  intro w _
  apply ((rmJetFamilySmooth_joint_closed h a b hab hh c k v).mul
    (rmJetFamilySmooth_joint_closed h a b hab hh c k w)).mul
  apply contDiffOn_prod
  intro j _
  exact inverseMetricFamilySmooth_joint_closed h a b hab hh c (v j) (w j)

theorem jetSq_smoothSpaceTime_closed (h : ℝ → HermitianField M) (a b : ℝ)
    (hab : a < b) (hh : MetricFamilySmooth h (Set.Icc a b)) (k : ℕ) :
    SmoothSpaceTime (fun x t => jetSq (h t) k x) (Set.Icc a b) := by
  intro c
  apply (chartJetSqFamilySmooth_joint_closed h a b hab hh c k).congr
  intro p hp
  exact jetSq_inChart (h p.2) (metricFamilySmooth_slice h hh hp.2) k c hp.1

theorem smoothSpaceTime_continuousOn {I : Set ℝ} {u : M.Carrier → ℝ → ℝ}
    (hu : SmoothSpaceTime u I) :
    ContinuousOn (fun p : M.Carrier × ℝ => u p.1 p.2) (Set.univ ×ˢ I) := by
  rintro ⟨x,t⟩ ht
  have hc : ContinuousWithinAt (fun p : ComplexVector n × ℝ => u (chartInv x p.1) p.2)
      (chartTarget x ×ˢ I) (chartPt x x,t) :=
    (hu x).continuousOn _ ⟨mem_extChartAt_target x,ht.2⟩
  have hmap : ContinuousAt (fun p : M.Carrier × ℝ => (chartPt x p.1,p.2)) (x,t) :=
    ((continuousAt_extChartAt (I := ComplexModel n) x).comp continuousAt_fst).prodMk
      continuousAt_snd
  have hnear : ∀ᶠ p : M.Carrier × ℝ in 𝓝 (x,t),
      p.1 ∈ (extChartAt (ComplexModel n) x).source :=
    (continuousAt_fst : ContinuousAt (fun p : M.Carrier × ℝ => p.1) (x,t)).eventually
      ((isOpen_extChartAt_source (I := ComplexModel n) x).mem_nhds (mem_extChartAt_source x))
  have hpre : (fun p : M.Carrier × ℝ => (chartPt x p.1,p.2)) ⁻¹' (chartTarget x ×ˢ I)
      ∈ 𝓝[Set.univ ×ˢ I] (x,t) := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with p hp hpI
    exact ⟨(extChartAt (ComplexModel n) x).map_source hp,hpI.2⟩
  have hcomp := hc.comp_of_preimage_mem_nhdsWithin
    (f := fun p : M.Carrier × ℝ => (chartPt x p.1,p.2)) hmap.continuousWithinAt hpre
  apply hcomp.congr_of_eventuallyEq_of_mem _ ht
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with p hp
  exact (congrArg (fun y => u y p.2) ((extChartAt (ComplexModel n) x).left_inv hp)).symm

theorem jetSq_continuousOn_closed (h : ℝ → HermitianField M) (a b : ℝ)
    (hab : a < b) (hh : MetricFamilySmooth h (Set.Icc a b)) (k : ℕ) :
    ContinuousOn (fun p : M.Carrier × ℝ => jetSq (h p.2) k p.1)
      (Set.univ ×ˢ Set.Icc a b) :=
  smoothSpaceTime_continuousOn (jetSq_smoothSpaceTime_closed h a b hab hh k)

end Yau.LeafProofs.L23Aux

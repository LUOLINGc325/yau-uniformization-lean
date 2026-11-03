import Yau.Geometry.Calculus

/-! Chart smoothness gives actual joint continuity at a closed time face. -/

open Filter Set
open scoped Topology ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_smooth_spacetime_continuousOn {I : Set ℝ} {u : M.Carrier → ℝ → ℝ}
    (hu : SmoothSpaceTime u I) :
    ContinuousOn (fun p : M.Carrier × ℝ => u p.1 p.2) (univ ×ˢ I) := by
  rintro ⟨x,t⟩ ht
  have hc : ContinuousWithinAt (fun p : ComplexVector n × ℝ => u (chartInv x p.1) p.2)
      (chartTarget x ×ˢ I) (chartPt x x,t) :=
    (hu x).continuousOn _ ⟨mem_extChartAt_target x,ht.2⟩
  have hmap : ContinuousAt (fun p : M.Carrier × ℝ => (chartPt x p.1,p.2)) (x,t) :=
    ((continuousAt_extChartAt (I := ComplexModel n) x).comp continuousAt_fst).prodMk continuousAt_snd
  have hnear : ∀ᶠ p : M.Carrier × ℝ in 𝓝 (x,t), p.1 ∈ (extChartAt (ComplexModel n) x).source :=
    (continuousAt_fst : ContinuousAt (fun p : M.Carrier × ℝ => p.1) (x,t)).eventually
      ((isOpen_extChartAt_source (I := ComplexModel n) x).mem_nhds (mem_extChartAt_source x))
  have hpre : (fun p : M.Carrier × ℝ => (chartPt x p.1,p.2)) ⁻¹' (chartTarget x ×ˢ I)
      ∈ 𝓝[univ ×ˢ I] (x,t) := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with p hp hpI
    exact ⟨(extChartAt (ComplexModel n) x).map_source hp,hpI.2⟩
  have hcomp := hc.comp_of_preimage_mem_nhdsWithin
    (f := fun p : M.Carrier × ℝ => (chartPt x p.1,p.2)) hmap.continuousWithinAt hpre
  apply hcomp.congr_of_eventuallyEq_of_mem _ ht
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with p hp
  exact (congrArg (fun y => u y p.2) ((extChartAt (ComplexModel n) x).left_inv hp)).symm

end Yau.Proofs.F05Aux

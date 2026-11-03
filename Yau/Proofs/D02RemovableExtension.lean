import Yau.Proofs.D02RemovableRegularity
import Mathlib.Analysis.Complex.RemovableSingularity

open scoped Manifold Topology ContDiff
open MeasureTheory Set Filter

noncomputable section
namespace Yau.NodeProofs.D02RemovableAux
open Yau Yau.Blueprint Yau.LeafProofs Yau.Blueprint.V03Proof Yau.NodeProofs.D02Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

/-- Once the actual limit is known, a single valid manifold chart and the weak
complex removable-singularity theorem give the extension with that SAME value. -/
theorem contMDiff_update_of_punctured_tendsto {f : ℂ → M.Carrier} {p : M.Carrier}
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) f puncturedUnitDisc)
    (hlim : Tendsto f (𝓝[≠] (0 : ℂ)) (𝓝 p)) :
    ContMDiffOn 𝓘(ℂ, ℂ) (ComplexModel n) ∞ (Function.update f 0 p) (Metric.ball 0 1) := by
  classical
  let fext := Function.update f (0 : ℂ) p
  have hfext0 : fext 0 = p := by simp [fext]
  have hc0 : ContinuousAt fext 0 := continuousAt_update_same.mpr hlim
  have hlocal : ∀ z : ℂ, z ≠ 0 → fext =ᶠ[𝓝 z] f := by
    intro z hz
    filter_upwards [eventually_ne_nhds hz] with w hw
    exact Function.update_of_ne hw _ _
  have hunit : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ puncturedUnitDisc := by
    have hu : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ Metric.ball 0 (1 : ℝ) :=
      Metric.ball_mem_nhds 0 (by norm_num)
    filter_upwards [hu.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hz0
    exact ⟨norm_pos_iff.mpr hz0, by simpa only [Metric.mem_ball, dist_zero_right] using hz⟩
  have hchart : ∀ᶠ z in 𝓝[≠] (0 : ℂ), fext z ∈ (extChartAt (ComplexModel n) p).source := by
    apply (hc0.eventually ((isOpen_extChartAt_source (I := ComplexModel n) p).mem_nhds ?_)).filter_mono
      nhdsWithin_le_nhds
    rw [hfext0]
    exact mem_extChartAt_source p
  have hd : ∀ᶠ z in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ (chartPt p ∘ fext) z := by
    filter_upwards [hunit, hchart, self_mem_nhdsWithin] with z hz hzc hz0
    have hzD : z ∈ puncturedCoordinateDomain f p := by
      refine ⟨hz, ?_⟩
      change f z ∈ (extChartAt (ComplexModel n) p).source
      simpa only [fext, Function.update_of_ne hz0] using hzc
    have hdf := (puncturedCoordinate_differentiableOn f hf p).differentiableAt
      ((puncturedCoordinateDomain_isOpen f hf p).mem_nhds hzD)
    exact hdf.congr_of_eventuallyEq ((hlocal z hz0).fun_comp (chartPt p))
  have hcoordc : ContinuousAt (chartPt p ∘ fext) 0 := by
    apply (continuousAt_extChartAt' (I := ComplexModel n) (x := p) (by
      rw [hfext0]
      exact mem_extChartAt_source p)).comp hc0
  have hcoord : ContDiffAt ℂ ∞ (chartPt p ∘ fext) 0 :=
    (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd hcoordc).contDiffAt
  have hm0 : ContMDiffAt 𝓘(ℂ, ℂ) (ComplexModel n) ∞ fext 0 := by
    rw [contMDiffAt_iff_target, hfext0]
    exact ⟨hc0, hcoord.contMDiffAt⟩
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    exact hm0.contMDiffWithinAt
  · have hzunit : z ∈ puncturedUnitDisc :=
      ⟨norm_pos_iff.mpr hz0, by simpa only [Metric.mem_ball, dist_zero_right] using hz⟩
    exact ((punctured_curve_contMDiffAt hf hzunit).congr_of_eventuallyEq (hlocal z hz0)).contMDiffWithinAt

end Yau.NodeProofs.D02RemovableAux

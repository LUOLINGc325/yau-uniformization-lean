import Yau.Proofs.P03RadialKernel

open scoped Topology ContDiff
open Set Filter MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ}

/-- A continuous function on an open set has a compact continuous global
model with the same germ at any chosen point of that set. -/
theorem exists_continuous_compact_model {U : Set (ComplexVector n)} (hU : IsOpen U)
    {f : ComplexVector n → ℂ} (hf : ContinuousOn f U) {a : ComplexVector n} (ha : a ∈ U) :
    ∃ F : ComplexVector n → ℂ, Continuous F ∧ HasCompactSupport F ∧ F =ᶠ[𝓝 a] f := by
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  let b : ContDiffBump a := ⟨R / 4, R / 2, by positivity, by linarith⟩
  let F : ComplexVector n → ℂ := fun x => b x • f x
  have hbU : tsupport (b : ComplexVector n → ℝ) ⊆ U := by
    rw [b.tsupport_eq]
    intro x hx
    exact hRU (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx).trans_lt (by dsimp [b]; linarith)))
  have hFc : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x ∈ tsupport (b : ComplexVector n → ℝ)
    · exact b.continuous.continuousAt.smul (hf.continuousAt (hU.mem_nhds (hbU hx)))
    · have he : F =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
        filter_upwards [(isClosed_tsupport (b : ComplexVector n → ℝ)).isOpen_compl.mem_nhds hx]
          with y hy
        change b y • f y = 0
        rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
      exact continuousAt_const.congr_of_eventuallyEq he
  have hsupport : tsupport F ⊆ tsupport (b : ComplexVector n → ℝ) :=
    tsupport_smul_subset_left b f
  refine ⟨F, hFc, b.hasCompactSupport.isCompact.of_isClosed_subset (isClosed_tsupport F) hsupport, ?_⟩
  filter_upwards [b.eventuallyEq_one] with x hx
  change b x • f x = f x
  change b x = 1 at hx
  rw [hx, one_smul]

end Yau.NodeProofs.P03Aux

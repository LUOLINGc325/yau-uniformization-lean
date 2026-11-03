import Yau.Proofs.P03RealSmoothing
import Yau.Proofs.P03RadialKernel
import Yau.Proofs.P03RadialMean
import Yau.Proofs.P03ApproxKernels
import Yau.Proofs.P03ConvolutionAssoc

open scoped Topology ContDiff
open MeasureTheory Filter

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ}

/-- The representative is an explicit fixed smooth convolution. Ordinary
shrinking kernels identify it AE via commutation and radial reproduction;
no holomorphic-limit or elliptic-regularity premise is used. -/
theorem local_holomorphic_representative
    {u : ComplexVector n → ℂ} {a : ComplexVector n} {r : ℝ}
    {U : Set (ComplexVector n)} (hr : 0 < r)
    (hKU : Metric.closedBall a (4 * r) ⊆ U)
    (huK : MemLp u 2 ((volume : Measure (ComplexVector n)).restrict
      (Metric.closedBall a (4 * r))))
    (hweak : ∀ (i : Fin n) (ψ : ComplexVector n → ℂ),
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ y, u y * wirtBar ψ y (stdVec i)) = 0) :
    ∃ g : ComplexVector n → ℂ, ContDiff ℝ ∞ g ∧
      DifferentiableOn ℂ g (Metric.ball a (3 * r)) ∧
      u =ᵐ[(volume : Measure (ComplexVector n)).restrict (Metric.ball a (2 * r))] g := by
  let K := Metric.closedBall a (4 * r)
  let f := K.indicator u
  let κ := radialKernel (n := n) r
  let g := smoothBy κ f
  have hf : Integrable f volume :=
    integrable_indicator_of_compact_memLp K (isCompact_closedBall _ _) huK
  have hk : ContDiff ℝ ∞ κ := radialKernel_contDiff r
  have hkc : HasCompactSupport κ := radialKernel_hasCompactSupport hr
  have hks : tsupport κ ⊆ Metric.closedBall 0 r := radialKernel_tsupport_subset hr
  have hg : ContDiff ℝ ∞ g := smoothBy_contDiff hf hk hkc
  have hgH : DifferentiableOn ℂ g (Metric.ball a (3 * r)) :=
    interior_real_smoothing_holomorphic hKU huK hweak hk hkc hks
  have hmH (j : ℕ) : DifferentiableOn ℂ
      (smoothBy (shrinkingKernel r hr j) f) (Metric.ball a (3 * r)) :=
    interior_real_smoothing_holomorphic hKU huK hweak (shrinkingKernel_contDiff hr j)
      (shrinkingKernel_hasCompactSupport hr j) (shrinkingKernel_tsupport_subset hr j)
  have hident (j : ℕ) (x : ComplexVector n) (hx : x ∈ Metric.ball a (2 * r)) :
      smoothBy (shrinkingKernel r hr j) f x = smoothBy (shrinkingKernel r hr j) g x := by
    calc
      smoothBy (shrinkingKernel r hr j) f x =
          smoothBy κ (smoothBy (shrinkingKernel r hr j) f) x :=
        (radial_smoothing_eq hk.continuous hkc hks (radialKernel_integral hr)
          (radialKernel_rotation r) (shrinkingSmoothing_contDiff hf hr j).continuous (hmH j) hx).symm
      _ = smoothBy (shrinkingKernel r hr j) g x :=
        congrFun (smoothBy_commute hf hk.continuous hkc
          (shrinkingKernel_contDiff hr j).continuous (shrinkingKernel_hasCompactSupport hr j)) x
  have hmAE := shrinkingKernel_ae_tendsto hf hr
  have hmAE' : ∀ᵐ x ∂(volume : Measure (ComplexVector n)).restrict (Metric.ball a (2 * r)),
      Tendsto (fun j => smoothBy (shrinkingKernel r hr j) f x) atTop (𝓝 (f x)) :=
    ae_restrict_of_ae hmAE
  refine ⟨g, hg, hgH, ?_⟩
  filter_upwards [hmAE', ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hfx hx
  have heq : (fun j => smoothBy (shrinkingKernel r hr j) f x) =
      (fun j => smoothBy (shrinkingKernel r hr j) g x) := funext fun j => hident j x hx
  rw [heq] at hfx
  have hgx := shrinkingKernel_tendsto_continuous hg.continuous hr x
  have he : f x = g x := tendsto_nhds_unique hfx hgx
  have hxK : x ∈ K := by
    apply Metric.mem_closedBall.mpr
    have hdx := Metric.mem_ball.mp hx
    linarith
  simpa only [f, Set.indicator_of_mem hxK] using he

end Yau.NodeProofs.P03Aux

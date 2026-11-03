import Yau.Proofs.V03BoundaryDerivative
import Yau.Proofs.V03CompactFiber

/-! The genuine angular derivative of a closed-disc trace converges
uniformly under radial approximation, from local C² at the circle. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem angularWithinDerivative_at_one_continuous {f : ℂ → ℝ}
    (hf : ∀ θ, ContDiffWithinAt ℝ 2 f (Metric.closedBall 0 1) (circlePoint θ)) :
    Continuous (angularWithinDerivative f 1) := by
  rw [continuous_iff_continuousAt]
  intro θ
  have hA := angularWithinDerivative_continuousWithinAt θ (hf θ)
  have hs : Continuous (fun t : ℝ => ((1 : ℝ), t)) := continuous_const.prodMk continuous_id
  have hh := hA.comp hs.continuousAt.continuousWithinAt
    (fun t (_ : t ∈ (Set.univ : Set ℝ)) => ⟨by simp, Set.mem_univ _⟩)
  simpa only [ContinuousAt, ContinuousWithinAt, Function.comp_def, nhdsWithin_univ] using hh

theorem angularWithinDerivative_tendstoUniformlyOn {f : ℂ → ℝ}
    (hf : ∀ θ, ContDiffWithinAt ℝ 2 f (Metric.closedBall 0 1) (circlePoint θ)) :
    TendstoUniformlyOn (angularWithinDerivative f) (angularWithinDerivative f 1)
      (𝓝[Set.Icc 0 1] 1) (Set.Icc 0 (2 * Real.pi)) :=
  tendstoUniformlyOn_of_continuousWithinAt_fiber isCompact_Icc
    (fun θ _ => angularWithinDerivative_continuousWithinAt θ (hf θ))
    (fun θ _ => (angularWithinDerivative_at_one_continuous hf).continuousAt)

theorem admissible_logWall_angular_uniform {n q : ℕ} {X : KahlerManifold n}
    {d : VariationData X q} (hd : VariationSetup d) {j : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) :
    TendstoUniformlyOn
      (angularWithinDerivative (fun ζ => Real.log (wallProduct d j (F.f ζ))))
      (angularWithinDerivative (fun ζ => Real.log (wallProduct d j (F.f ζ))) 1)
      (𝓝[Set.Icc 0 1] 1) (Set.Icc 0 (2 * Real.pi)) :=
  angularWithinDerivative_tendstoUniformlyOn fun θ =>
    (admissible_logWall_contDiffWithinAt hd hF θ).of_le (by simp)

end Yau.Blueprint.V03Proof

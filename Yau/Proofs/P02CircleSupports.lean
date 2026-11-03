import Yau.Proofs.P02PlanarComparison

noncomputable section
open Filter Metric
open scoped Topology

namespace Yau.NodeProofs.P02Aux
open Yau Yau.LeafProofs L22Aux

theorem complexLinePshOn_of_lower_supports {n : ℕ} (O : Set (ComplexVector n))
    (f : ComplexVector n → ℝ) (hfc : ContinuousOn f O)
    (hsupport : ∀ a ∈ O, ∃ s : ComplexVector n → ℝ,
      ContDiffAt ℝ 2 s a ∧ s a=f a ∧
        (∀ᶠ y in 𝓝 a, s y ≤ f y) ∧
        ∀ v, 0 ≤ complexLeviQuadratic s a v) : LeafCandidates.ComplexLinePshOn O f := by
  refine ⟨hfc,?_⟩
  intro z w hdisc
  let T : ℂ → ComplexVector n := fun ζ => z+ζ • w
  have hT : Continuous T := by fun_prop
  have hTd : ContDiff ℝ 2 T := by fun_prop
  have hTO : Set.MapsTo T (closedBall (0 : ℂ) 1) O := by
    intro ζ hζ
    exact hdisc ζ (by simpa only [mem_closedBall,dist_zero_right] using hζ)
  have H := planar_submean_of_lower_supports (f ∘ T)
    (hfc.comp hT.continuousOn hTO) (fun a ha => by
      obtain ⟨s,hsc,hs0,hsbelow,hspos⟩ := hsupport (T a) (hTO (ball_subset_closedBall ha))
      refine ⟨s ∘ T,hsc.comp a hTd.contDiffAt,hs0,?_,?_⟩
      · exact hT.continuousAt.eventually hsbelow
      · change 0 ≤ planarTrace (fun ζ : ℂ => s (z+ζ • w)) a
        rw [planarTrace_complexAffine s z w a hsc]
        exact mul_nonneg (by norm_num) (hspos w))
  simpa only [Function.comp_def,T,zero_smul,add_zero] using H

end Yau.NodeProofs.P02Aux

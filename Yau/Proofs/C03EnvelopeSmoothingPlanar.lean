import Yau.Proofs.P02PlanarComparison
import Yau.Blueprint.Nodes

/-! Genuine separate planar lower supports imply the frozen affine-disc psh predicate. -/
noncomputable section
open scoped Topology ContDiff Matrix ComplexOrder
open Filter Metric Set
namespace Yau.Proofs.C03Aux.EnvelopeSmoothing
open Yau Yau.Blueprint Yau.LeafProofs L22Aux Yau.NodeProofs.P02Aux
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

/-- No common support in all directions is assumed. -/
def PlanarLowerSupports {n : ℕ} (f : ComplexVector n → ℝ)
    (O : Set (ComplexVector n)) (B : ComplexVector n → ComplexVector n → ℝ) : Prop :=
  ∀ z ∈ O, ∀ v : ComplexVector n,
    ∃ s : ℂ → ℝ, ContDiffAt ℝ 2 s 0 ∧ s 0 = f z ∧
      (∀ᶠ a in 𝓝 0, s a ≤ f (z + a • v)) ∧ B z v ≤ planarTrace s 0

theorem planarTrace_sub_const (f : ℂ → ℝ) (a b : ℂ) :
    planarTrace (fun z => f (z - a)) b = planarTrace f (b - a) := by
  have hD : fderiv ℝ (fun z => f (z - a)) = fun z => fderiv ℝ f (z - a) :=
    funext (fun _ => fderiv_comp_sub a)
  simp only [planarTrace, hD, fderiv_comp_sub]

theorem complexLinePshOn_of_planar_lower_supports {n : ℕ}
    (O : Set (ComplexVector n)) (f : ComplexVector n → ℝ)
    (hfc : ContinuousOn f O) (hsupport : PlanarLowerSupports f O (fun _ _ => 0)) :
    LeafCandidates.ComplexLinePshOn O f := by
  refine ⟨hfc, ?_⟩
  intro z v hdisc
  let T : ℂ → ComplexVector n := fun a => z + a • v
  have hT : Continuous T := by
    change Continuous (fun a : ℂ => WithLp.toLp 2 (fun i => z i + a * v i))
    exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp
      (continuous_pi fun _ => continuous_const.add (continuous_id.mul continuous_const))
  have hTO : MapsTo T (closedBall (0 : ℂ) 1) O := by
    intro a ha
    exact hdisc a (by simpa only [mem_closedBall, dist_zero_right] using ha)
  have hmean := planar_submean_of_lower_supports (f ∘ T)
    (hfc.comp hT.continuousOn hTO) (fun a ha => by
      obtain ⟨s, hsc, hs0, hsnear, hstrace⟩ := hsupport (T a)
        (hTO (ball_subset_closedBall ha)) v
      have ht : Tendsto (fun b : ℂ => b - a) (𝓝 a) (𝓝 0) := by
        have hc : Continuous (fun b : ℂ => b - a) := continuous_id.sub continuous_const
        simpa only [ContinuousAt, sub_self] using hc.continuousAt (x := a)
      refine ⟨fun b => s (b - a), ?_, ?_, ?_, ?_⟩
      · have hs' : ContDiffAt ℝ 2 s (a - a) := by simpa only [sub_self] using hsc
        exact hs'.comp (f := fun b : ℂ => b - a) a (contDiffAt_id.sub contDiffAt_const)
      · simpa only [sub_self, Function.comp_apply] using hs0
      · filter_upwards [ht.eventually hsnear] with b hb
        have heq : T a + (b - a) • v = T b := by
          dsimp only [T]
          rw [sub_smul]
          abel
        rw [heq] at hb
        exact hb
      · simpa only [planarTrace_sub_const, sub_self] using hstrace)
  simpa only [T, Function.comp_def, zero_smul, add_zero] using hmean

theorem isPshOn_of_complexLinePshOn {n : ℕ} {O : Set (ComplexVector n)}
    {f : ComplexVector n → ℝ} (hf : LeafCandidates.ComplexLinePshOn O f) :
    IsPshOn (fun z => (f z : EReal)) O := by
  refine ⟨fun _ _ => by simp, ?_, ?_⟩
  · exact (continuous_coe_real_ereal.comp_continuousOn hf.1).upperSemicontinuousOn
  · intro z v hdisc φ hφ hmajor
    apply EReal.coe_le_coe_iff.mpr
    exact (hf.2 z v hdisc).trans (circleAverage_mono
      (continuous_affine_circle hf.1 z v hdisc) hφ
      (fun θ => EReal.coe_le_coe_iff.mp (hmajor θ)))

theorem isPshOn_of_planar_lower_supports {n : ℕ}
    (O : Set (ComplexVector n)) (f : ComplexVector n → ℝ)
    (hfc : ContinuousOn f O) (hsupport : PlanarLowerSupports f O (fun _ _ => 0)) :
    IsPshOn (fun z => (f z : EReal)) O :=
  isPshOn_of_complexLinePshOn (complexLinePshOn_of_planar_lower_supports O f hfc hsupport)

end Yau.Proofs.C03Aux.EnvelopeSmoothing

import Yau.Proofs.D02DiscMobiusInverse
import Yau.Proofs.D02AreaReparam

/-! One compact set contains every full closed image of every original
admissible base disc. The center compact is chosen before the varying
disc and point; actual disc automorphisms preserve its original area. -/

open scoped Topology Manifold ContDiff ENNReal
open MeasureTheory Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint

theorem baseDisc_family_enclosure_of_injective_immersion {n N : ℕ} (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    (hinj : Function.Injective F) {K : Set (Pt X)} (hK : IsCompact K) (A : ℝ) :
    ∃ K' : Set (Pt X), IsCompact K' ∧ ∀ f : ℂ → Pt X, IsHolomorphicDisc f →
      (∀ z : ℂ, ‖z‖ = 1 → f z ∈ K) → discArea X.metric.form f ≤ ENNReal.ofReal A →
      ∀ z : ℂ, ‖z‖ ≤ 1 → f z ∈ K' := by
  obtain ⟨Kc, hKc, hcenter⟩ := baseDisc_compact_centres X hF hImm hinj hK A
  refine ⟨Kc ∪ K, hKc.union hK, fun f hf hb harea z hz => ?_⟩
  rcases lt_or_eq_of_le hz with hzi | hzb
  · have hcomp := holomorphicDisc_comp_discMobius hf hzi
    have hbcomp : ∀ w : ℂ, ‖w‖ = 1 → (f ∘ discMobius z) w ∈ K :=
      fun w hw => hb (discMobius z w) (discMobius_norm_eq_one hzi hw)
    have hα : DifferentiableOn ℂ (discMobius z) (ball (0 : ℂ) 1) :=
      ((discMobius_contDiffOn hzi).mono ball_subset_closedBall).differentiableOn (by simp)
    have hareaEq := D02AreaReparamAux.discArea_comp_of_bijOn X.metric.form hf hα (discMobius_bijOn_ball hzi)
    have hcompArea : discArea X.metric.form (f ∘ discMobius z) ≤ ENNReal.ofReal A := by
      rw [hareaEq]
      exact harea
    have hzKc := hcenter (f ∘ discMobius z) hcomp hbcomp hcompArea
    exact Or.inl (by simpa only [Function.comp_apply, discMobius_zero] using hzKc)
  · exact Or.inr (hb z hzb)

end Yau.NodeProofs.D02Aux

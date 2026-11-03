import Yau.Proofs.F05CornerSmooth
import Yau.Proofs.F05AtlasCompactness

/-! A single actual compact-domain curvature bound chooses the paper's
corner scale uniformly before every boundary point and every time. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.Blueprint Yau.F05Transport
variable {n : ℕ} {X : KahlerManifold n}

theorem F05_flow_corner_uniform_bounds {O : Set (Pt X)} {A : AtlasData X.manifold}
    (hA : GenuineAtlas O A) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) {a : ℝ} (ha : 0 < a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ζ : ℝ → ℝ,
      (∀ s, 0 ≤ ζ s ∧ ζ s ≤ 1) → (∀ s, 1 ≤ s → ζ s = 0) →
      ∀ x ∈ closure O, ∀ t : ℝ, 0 ≤ t →
        ρ x t+a/2 ≤ flowCornerBoundary X ρ a δ ζ x t ∧
          flowCornerBoundary X ρ a δ ζ x t ≤ ρ x t+a := by
  have hR := F05_flow_scalar_smooth o h U P ρ hloc (by norm_num : (0 : ℝ) < 1)
  have hR0 : SmoothFn (fun x => scalarCurvature X.metric.form x) := by
    simpa only [hloc.1.1] using smoothFn_slice hR (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl,by norm_num⟩)
  obtain ⟨B,hB⟩ := (F05_atlas_closure_compact hA).exists_bound_of_continuousOn
    (Yau.LeafProofs.L18Aux.continuous_of_smoothFn hR0).continuousOn
  obtain ⟨δ,hδ,hScale⟩ := exists_uniform_corner_scale a B ha
  refine ⟨δ,hδ,?_⟩
  intro ζ hζ hSupport x hx t ht
  have hRg : 0 ≤ scalarCurvature X.metric.form x := by
    simpa only [hloc.1.1] using (hloc.2.2.2.2.2.2.2.2.2.2.1 x 0 le_rfl).2
  have hUpper : scalarCurvature X.metric.form x ≤ B := (le_abs_self _).trans (hB x hx)
  exact cornerBoundary_bounds (ρ x) a (scalarCurvature X.metric.form x) δ t ζ ha.le hRg hδ ht hζ hSupport
    (hScale _ hUpper)

end Yau.Proofs.F05Aux

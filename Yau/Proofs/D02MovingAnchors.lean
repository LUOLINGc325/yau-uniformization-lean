import Yau.Proofs.D02MovingAnchorArea
import Yau.Proofs.D02RadialDistance
import Yau.Proofs.D02UniformImmersionConstants

/-! The actual moving positive-area anchors all map into one proper
same-metric ball, selected before the varying disc. The immersion potential
therefore has a common lower bound on these same measurable anchors. -/

open scoped Manifold Topology ContDiff ENNReal
open MeasureTheory Set

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.LeafProofs

theorem polarRay_norm_arg (z : ℂ) : polarRay ‖z‖ (Complex.arg z) = z := by
  simpa only [polarRay, Complex.polarCoord_symm_apply, Complex.ofReal_cos,
    Complex.ofReal_sin] using Complex.norm_mul_cos_add_sin_mul_I z

theorem uniform_movingAnchor_compact {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) {K : Set M.Carrier} (hK : IsCompact K) (A : ℝ) :
    ∃ K₁ : Set M.Carrier, IsCompact K₁ ∧
      ∀ f : ℂ → M.Carrier, IsHolomorphicDisc f →
        (∀ z : ℂ, ‖z‖ = 1 → f z ∈ K) →
        discArea g.form f ≤ ENNReal.ofReal A →
        let S := anchorAnnulus (goodAngles (discEnergyDensity g.form f) A)
        MeasurableSet S ∧ ENNReal.ofReal (5 * Real.pi / 32) ≤ volume S ∧
          S ⊆ {z : ℂ | (1 / 2 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 4} ∧
          ∀ z ∈ S, f z ∈ K₁ := by
  classical
  let o : M.Carrier := Classical.choice (inferInstance : Nonempty M.Carrier)
  obtain ⟨R, hR⟩ := hK.bddAbove_image (L12Aux.continuous_distFrom g o).continuousOn
  let K₁ : Set M.Carrier := {y | inducedDistance g.form o y ≤ R + (2 * radialEnergyThreshold A + 1)}
  refine ⟨K₁, L12Aux.isCompact_inducedDistance_sublevel g o _, ?_⟩
  intro f hf hb harea
  obtain ⟨hS, hvol, hcompact⟩ := disc_movingAnchorArea g hf A harea
  refine ⟨hS, hvol, hcompact, fun z hz => ?_⟩
  let θ := Complex.arg z
  let w := polarRay 1 θ
  have hw : ‖w‖ = 1 := by simp [w, polarRay_norm]
  have hradial := goodAngle_radialDistance g hf A hz.2.2 hz.1.le
    (hz.2.1.trans (by norm_num : (3 / 4 : ℝ) < 1))
  rw [polarRay_norm_arg] at hradial
  have hboundary : distFrom g.form o (f w) ≤ R :=
    hR (Set.mem_image_of_mem (distFrom g.form o) (hb w hw))
  have htriangle := g.induced_distance_triangle o (f w) (f z)
  rw [g.induced_distance_symm (f w) (f z)] at htriangle
  change inducedDistance g.form o (f z) ≤ R + (2 * radialEnergyThreshold A + 1)
  exact htriangle.trans (add_le_add hboundary hradial)

/-- The same ψ and the same positive-area anchors give the D04 noncollapse data. -/
theorem uniform_movingAnchor_potential {n N : ℕ} (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    {K : Set (Pt X)} (hK : IsCompact K) (A : ℝ) :
    ∃ K₁ : Set (Pt X), ∃ C : ℝ, IsCompact K₁ ∧ 0 ≤ C ∧
      ∀ f : ℂ → Pt X, IsHolomorphicDisc f →
        (∀ z : ℂ, ‖z‖ = 1 → f z ∈ K) →
        discArea X.metric.form f ≤ ENNReal.ofReal A →
        let S := anchorAnnulus (goodAngles (discEnergyDensity X.metric.form f) A)
        MeasurableSet S ∧ ENNReal.ofReal (5 * Real.pi / 32) ≤ volume S ∧
          S ⊆ {z : ℂ | (1 / 2 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 4} ∧
          ∀ z ∈ S, f z ∈ K₁ ∧ -C ≤ immersionPotential X.metric.form F (f z) := by
  obtain ⟨K₁, hK₁, hanchors⟩ := uniform_movingAnchor_compact X.metric hK A
  have hu := L18Aux.continuous_of_smoothFn (immersionPotential_smooth X.metric.form
    (L12Aux.metricSmooth_of_smoothMetric X.metric) hF hImm)
  obtain ⟨b, hb⟩ := hK₁.bddBelow_image hu.continuousOn
  refine ⟨K₁, max (-b) 0, hK₁, le_max_right _ _, ?_⟩
  intro f hf hboundary harea
  obtain ⟨hS, hvol, hcompact, hmap⟩ := hanchors f hf hboundary harea
  refine ⟨hS, hvol, hcompact, fun z hz => ⟨hmap z hz, ?_⟩⟩
  have hlower := hb (Set.mem_image_of_mem (immersionPotential X.metric.form F) (hmap z hz))
  linarith [le_max_left (-b) 0]

end Yau.NodeProofs.D02Aux

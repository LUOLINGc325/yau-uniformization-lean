import Yau.Proofs.F01ControlledRayleighOrder

/-! The actual controlled exhaustion supplies properness and every
background differential budget for Q on the full original closed slab. -/
noncomputable section
open Set
open scoped ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ}

theorem controlled_short_time_comparison_Q (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) {L : ℝ} (ho : u o < L) :
    let N := sublevelManifold X.manifold u hu.1 o L ho
    let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
    ∀ (h : ℝ → HermitianField N) (U : N.Carrier → ℝ → ℝ) (T C D c : ℝ),
      0 < T → 1 ≤ C → 0 ≤ D → 0 ≤ c →
      MetricFamilySmooth h (Icc 0 T) → SmoothSpaceTime U (Icc 0 T) →
      h 0 = α → (∀ x, U x 0 = 0) →
      (∀ x t, t ∈ Icc 0 T → (gMat (h t) x - ((C⁻¹ : ℝ) : ℂ) • gMat α x).PosSemidef) →
      (∀ x t, t ∈ Icc 0 T → ((C : ℂ) • gMat α x - gMat (h t) x).PosSemidef) →
      (∀ s ∈ Icc 0 T, ∀ x,
        gMat (h s) x = gMat α x - (s : ℂ) • ricci α x + levi (fun y => U y s) x) →
      (∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
        (flowLogDetRatio α h x s) (Icc 0 T) s) →
      ∀ φ : N.Carrier → ℝ, SmoothFn φ → (∀ x, φ x ≤ 0) →
      (∀ x, (gMat α x - (D : ℂ) • ricci α x +
        (D : ℂ) • levi φ x - (c : ℂ) • gMat α x).PosSemidef) →
      SmoothSpaceTime (comparisonFunction D n U (flowLogDetRatio α h) φ) (Icc 0 T) ∧
      ∀ x t, t ∈ Icc 0 T →
        0 ≤ comparisonFunction D n U (flowLogDetRatio α h) φ x t ∧
        c * traceWith (gMat (h t) x) (gMat α x) ≤
          fieldHeatWithin h (Icc 0 T)
            (fun s y => comparisonFunction D n U (flowLogDetRatio α h) φ y s) x t := by
  dsimp only
  intro h U T C D c hT hC hD hc hh hU hh0 hU0 hlo hhi hpot hpde φ hφ hφsign hweight
  obtain ⟨A, hA, B, hB, hbudgets⟩ := controlled_conformal_gradient_levi X o u hu
  have hL : 0 < L := (zero_lt_one.trans_le (hu.2.2.1 o)).trans ho
  let N := sublevelManifold X.manifold u hu.1 o L ho
  let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
  let f : N.Carrier → ℝ := approximatingScalar X.manifold u hu.1 o L ho
  have hf : SmoothFn f := approximatingScalar_smoothFn u hu.1 o hL ho
  have hf0 (x : N.Carrier) : 0 ≤ f x :=
    conformalProfile_nonneg ((div_lt_one hL).mpr
      (sublevelManifold_point_level X.manifold u hu.1 o L ho x))
  have hfproper : ∀ b : ℝ, IsCompact {x : N.Carrier | f x ≤ b} :=
    conformalProfile_compact_component_sublevel u (continuous_of_smoothFn hu.1) hu.2.1 o hL
  exact short_time_comparison_Q α (controlled_background_geometry X o u hu ho).1 h U
    hT hC hD hc (div_nonneg hB.le (sq_nonneg L)) hh hU hh0 hU0 hlo hhi hpot hpde
    φ hφ hφsign hweight f hf hf0 hfproper (fun x => (hbudgets L ho x).2.2)

end Yau.NodeProofs.F01Aux

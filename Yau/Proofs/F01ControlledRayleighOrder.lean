import Yau.Proofs.F01ControlledConformalBounds
import Yau.Proofs.F01ApproximatingRicci
import Yau.Proofs.F01ConformalCompactSublevels
import Yau.Proofs.F01RayleighMetricUpperBound
import Yau.Proofs.F01ShortTimeQComparison
import Yau.Proofs.F01ContactScale
import Yau.Proofs.F01AmbientBisectionalNonneg

/-! The original controlled exhaustion supplies every conformal budget
and properness input of the actual Rayleigh argument. One level threshold
precedes every short-time solution, weight and comparison interval. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ}

theorem controlled_rayleigh_order (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) {c : ℝ} (hc : 0 < c) :
    ∃ L0 : ℝ, 0 < L0 ∧ ∀ (L : ℝ), L0 ≤ L → ∀ (ho : u o < L),
    let N := sublevelManifold X.manifold u hu.1 o L ho
    let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
    ∀ (h : ℝ → HermitianField N) (U : N.Carrier → ℝ → ℝ) (Tsol T C D : ℝ),
      0 < T → T < Tsol → 1 ≤ C → 0 ≤ D →
      MetricFamilySmooth h (Icc 0 Tsol) → SmoothSpaceTime U (Icc 0 Tsol) →
      h 0 = α → (∀ x, U x 0 = 0) →
      (∀ x t, t ∈ Icc 0 Tsol → (gMat (h t) x - ((C⁻¹ : ℝ) : ℂ) • gMat α x).PosSemidef) →
      (∀ x t, t ∈ Icc 0 Tsol → ((C : ℂ) • gMat α x - gMat (h t) x).PosSemidef) →
      (∀ s ∈ Icc 0 Tsol, ∀ x,
        gMat (h s) x = gMat α x - (s : ℂ) • ricci α x + levi (fun y => U y s) x) →
      (∀ x s, s ∈ Icc 0 Tsol → HasDerivWithinAt (U x)
        (flowLogDetRatio α h x s) (Icc 0 Tsol) s) →
      ∀ φ : N.Carrier → ℝ, SmoothFn φ → (∀ x, φ x ≤ 0) →
      (∀ x, (gMat α x - (D : ℂ) • ricci α x + (D : ℂ) • levi φ x - (c : ℂ) • gMat α x).PosSemidef) →
      ∀ x t, t ∈ Icc 0 T →
        ((Real.exp (rayleighPenalty L⁻¹ (comparisonFunction D n U (flowLogDetRatio α h) φ x t)) : ℂ) •
          gMat α x - gMat (h t) x).PosSemidef := by
  obtain ⟨A, hA, B, hB, hbudgets⟩ := controlled_conformal_gradient_levi X o u hu
  obtain ⟨L0, hL0, hscale⟩ := exists_uniform_contact_threshold hB.le (sq_nonneg A) hc
  refine ⟨L0, hL0, ?_⟩
  intro L hLL0 ho
  dsimp only
  intro h U Tsol T C D hT hTsol hC hD hh hU hh0 hU0 hlo hhi hpot hpde φ hφ hφsign hweight
  let S := sublevelOpens X.manifold u hu.1 o L
  let hS := sublevelComponent_isConnected ho
  let N := sublevelManifold X.manifold u hu.1 o L ho
  let f : N.Carrier → ℝ := approximatingScalar X.manifold u hu.1 o L ho
  let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
  let Q : N.Carrier → ℝ → ℝ := comparisonFunction D n U (flowLogDetRatio α h) φ
  have hL : 0 < L := hL0.trans_le hLL0
  have hf : SmoothFn f := approximatingScalar_smoothFn u hu.1 o hL ho
  have hf0 (x : N.Carrier) : 0 ≤ f x :=
    conformalProfile_nonneg ((div_lt_one hL).mpr
      (sublevelManifold_point_level X.manifold u hu.1 o L ho x))
  have hfproper : ∀ b : ℝ, IsCompact {x : N.Carrier | f x ≤ b} :=
    conformalProfile_compact_component_sublevel u (continuous_of_smoothFn hu.1) hu.2.1 o hL
  have hα : MetricSmooth α := (controlled_background_geometry X o u hu ho).1
  have hsub : Icc 0 T ⊆ Icc 0 Tsol := fun t ht => ⟨ht.1, ht.2.trans hTsol.le⟩
  have hhCmp : MetricFamilySmooth h (Icc 0 T) := fun x i j =>
    (hh x i j).mono (prod_mono Subset.rfl hsub)
  have hUCmp : SmoothSpaceTime U (Icc 0 T) := fun x =>
    (hU x).mono (prod_mono Subset.rfl hsub)
  have hQ := short_time_comparison_Q α hα h U hT hC hD hc.le
    (div_nonneg hB.le (sq_nonneg L)) hhCmp hUCmp hh0 hU0
    (fun x t ht => hlo x t (hsub ht)) (fun x t ht => hhi x t (hsub ht))
    (fun s hs => hpot s (hsub hs)) (fun x s hs => (hpde x s (hsub hs)).mono hsub)
    φ hφ hφsign hweight f hf hf0 hfproper (fun x => (hbudgets L ho x).2.2)
  have hnegative (δ : ℝ) (hδ : δ ≤ 1) :
      (3 * (B / L ^ 2) + 3 * (A ^ 2 / L ^ 2)) - c * L⁻¹ +
        8 * (A ^ 2 / L ^ 2) + δ * (B / L ^ 2 + 2 * (A ^ 2 / L ^ 2)) < 0 := by
    convert hscale L hLL0 δ hδ using 1 <;> ring
  exact rayleigh_metric_upper_bound X.manifold S hS X.metric (kahlerManifold_nonnegBisectional X)
    f hf hf0 hfproper h U Q hT hTsol hh hU hh0 hpot hpde (zero_lt_one.trans_le hC)
    (fun t ht x => hhi x t (hsub ht)) hQ.1 (fun x t ht => (hQ.2 x t ht).1)
    (inv_pos.mpr hL) hc.le (div_nonneg hB.le (sq_nonneg L))
    (div_nonneg (sq_nonneg A) (sq_nonneg L))
    (fun x => (hbudgets L ho x).1) (fun x => (hbudgets L ho x).2.1)
    (fun x => (hbudgets L ho x).2.2) (fun x t ht => (hQ.2 x t ht).2)
    (fun δ hδ hδone => hnegative δ hδone)

end Yau.NodeProofs.F01Aux

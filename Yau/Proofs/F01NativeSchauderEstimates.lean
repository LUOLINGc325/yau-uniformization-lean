import Yau.Proofs.F01InitialSchauderTransfer
import Yau.Proofs.F01InteriorSchauderTransfer
import Yau.LeafProofs.L05
import Yau.LeafProofs.L16InteriorLinearSchauder

/-! The actual original analytic producers discharge both internal
estimate parameters. Numerical constants still precede every flow,
chart center and rescaled linear equation. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem normalized_initial_schauder
    (g : HermitianField M) (hg : MetricSmooth g) (A : BoundedChartFamily g)
    {C α β : ℝ} (hC : 1 ≤ C) (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) :
    ∃ Cv : ℝ, 0 < Cv ∧
      ∀ (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) (T ρ : ℝ),
      0 < ρ → 2 * ρ ≤ A.radius → 2 * ρ ≤ 1 → (2 * ρ) ^ 2 ≤ T →
      SmoothSpaceTime U (Icc 0 T) → h 0 = g → (∀ x, U x 0 = 0) →
      (∀ s ∈ Icc 0 T, ∀ x,
        gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x) →
      (∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
        (flowLogDetRatio g h x s) (Icc 0 T) s) →
      (∀ x s, s ∈ Icc 0 T →
        (gMat (h s) x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
        ((C : ℂ) • gMat g x - gMat (h s) x).PosSemidef) →
      ∀ a : M.Carrier,
      SchauderBound (min α β) (cylinder (ball 0 1) (-1) 1)
        (forwardZeroSpaceTime (parabolicRescalePotential ρ
          (fun p : Point n => U (A.chart a p.1) p.2))) Cv := by
  exact normalized_initial_schauder_of_estimate (Yau.LeafProofs.L05).2.2
    g hg A hC hα hα1 hβ hβ1

theorem interior_schauder_affine
    (hn : 0 < n)
    {β ell upper M : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hM : 0 < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Set (Space n)) (l r ρ τ : ℝ) (c : Space n)
      (A : Point n → Mat n) (u f : Point n → ℝ) (F B : ℝ),
      |ρ| ≤ 1 →
      MapsTo (fun x => ρ • x + c) (Metric.ball 0 2) S →
      MapsTo (fun t => τ + ρ ^ 2 * t) (Icc (-4) 0) (Icc l r) →
      Elliptic (cylinder S l r) A ell upper →
      HolderBound β (cylinder S l r) A M →
      HolderBound β (cylinder S l r) f F → C2 (cylinder S l r) u →
      (∀ p ∈ cylinder S l r, |u p| ≤ B) →
      (∀ p ∈ cylinder S l r, linearOp (cylinder S l r) A (fun _ _ => 0) u p = f p) →
      SchauderBound β (backward 1) (affineParabolicPullback ρ c τ u) (C * (B + F)) := by
  exact interior_schauder_affine_transfer
    Yau.LeafProofs.L16InteriorLinear.interiorLinearSchauder hn hβ hβ1 hM

end Yau.NodeProofs.F01Aux

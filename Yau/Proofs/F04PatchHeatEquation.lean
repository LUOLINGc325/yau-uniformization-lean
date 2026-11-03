import Yau.Proofs.F04ChartOperatorLocality

open Set
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.Blueprint

/-- A genuine smooth chart patch and its actual chart PDE give the
 physical heat equation at the center on EVERY supplied time face. No
 global smoothness across a finite spatial boundary is assumed. -/
theorem flow_heatOp_of_chart_patch
    {n : ℕ} (X : KahlerManifold n) (h : Yau.Blueprint.Flow X) (u f : STF X) (x : Pt X)
    {O : Set (Space n)} (hO : IsOpen O) (hxO : chartPt x x ∈ O) (I : Set ℝ)
    {v : Point n → ℝ} (hv : ContDiffOn ℝ ∞ v (O ×ˢ I))
    (he : EqOn (fun p : Point n => u (chartInv x p.1) p.2) v (O ×ˢ I))
    (hPDE : ∀ p ∈ O ×ˢ I,
      linearOp (O ×ˢ I) (flowChartPrincipal h x) (fun _ _ => 0) v p = f (chartInv x p.1) p.2) :
    ∀ t ∈ I, heatOp h I u x t = f x t := by
  intro t ht
  have hp : (chartPt x x,t) ∈ O ×ˢ I := ⟨hxO,ht⟩
  have hC2 : ContDiffAt ℝ 2 (inChart x (fun y => u y t)) (chartPt x x) :=
    spatialSlice_C2_of_eqOn hO he hv hp
  rw [flow_heatOp_chart_center X h u x hxO I t hC2,
    linearOp_congr_product_of_eqOn hO he hp,hPDE _ hp,
    Yau.LeafProofs.chartInv_chartPt_of_mem x x (mem_chart_source _ _)]

end Yau.F04Proof

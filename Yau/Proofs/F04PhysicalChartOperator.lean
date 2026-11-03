import Yau.Proofs.F04LocalChartOperator
import Yau.Blueprint.Stages

open Set
open scoped Topology ContDiff Manifold Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.Blueprint

/-- The physical heat operator is exactly the actual local real chart
 operator at the chart center, on ANY time set (including a closed face).
 Only the actual local spatial C2 germ is needed; a finite-domain function
 may be zero outside its domain without a false global smoothness premise. -/
theorem flow_heatOp_chart_center
    {n : ℕ} (X : KahlerManifold n) (h : Yau.Blueprint.Flow X) (u : STF X) (x : Pt X)
    {O : Set (Space n)} (hxO : chartPt x x ∈ O) (I : Set ℝ) (t : ℝ)
    (hC2 : ContDiffAt ℝ 2 (inChart x (fun y => u y t)) (chartPt x x)) :
    heatOp h I u x t = linearOp (O ×ˢ I) (flowChartPrincipal h x) (fun _ _ => 0)
      (fun p : Point n => u (chartInv x p.1) p.2) (chartPt x x,t) := by
  have hT : timeD (O ×ˢ I) (fun p : Point n => u (chartInv x p.1) p.2) (chartPt x x,t) =
      derivWithin (u x) I t := by
    have hFiber : {s : ℝ | (chartPt x x,s) ∈ O ×ˢ I} = I := by ext s; simp [hxO]
    rw [timeD,hFiber]
    change derivWithin (fun s => u (chartInv x (chartPt x x)) s) I t = derivWithin (u x) I t
    rw [Yau.LeafProofs.chartInv_chartPt_of_mem x x (mem_chart_source _ _)]
  have hLap : laplacian (h t) (fun y => u y t) x =
      ∑ i, ∑ j, flowChartPrincipal h x (chartPt x x,t) i j *
        spatialDD (fun p : Point n => u (chartInv x p.1) p.2) (chartPt x x,t) (realVec i) (realVec j) :=
    flowChartPrincipal_operator_center h x hC2 t
  unfold heatOp
  rw [hLap]
  simp only [linearOp,hT,zero_mul,Finset.sum_const_zero,sub_zero]


end Yau.F04Proof

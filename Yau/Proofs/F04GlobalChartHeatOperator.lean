import Yau.Proofs.F04ChartCoefficients
import Yau.Blueprint.Stages

open Set
open scoped Topology ContDiff Manifold Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.Blueprint

/-- A genuinely globally smooth spatial slice gives the actual heat
 operator in any fixed chart, at every chart point and on any time set. -/
theorem flow_heatOp_fixed_chart
    {n : ℕ} (X : KahlerManifold n) (h : Yau.Blueprint.Flow X) (u : STF X) (c : Pt X)
    {O : Set (Space n)} {z : Space n} (hzO : z ∈ O) (hzt : z ∈ chartTarget c)
    (I : Set ℝ) (t : ℝ) (hu : SmoothFn (fun x => u x t)) :
    heatOp h I u (chartInv c z) t = linearOp (O ×ˢ I) (flowChartPrincipal h c) (fun _ _ => 0)
      (fun p : Point n => u (chartInv c p.1) p.2) (z,t) := by
  have hT : timeD (O ×ˢ I) (fun p : Point n => u (chartInv c p.1) p.2) (z,t) =
      derivWithin (u (chartInv c z)) I t := by
    have hFiber : {s : ℝ | (z,s) ∈ O ×ˢ I} = I := by ext s; simp [hzO]
    rw [timeD,hFiber]
  have hLap : laplacian (h t) (fun x => u x t) (chartInv c z) =
      ∑ i, ∑ j, flowChartPrincipal h c (z,t) i j *
        spatialDD (fun p : Point n => u (chartInv c p.1) p.2) (z,t) (realVec i) (realVec j) :=
    flowChartPrincipal_operator h c hu z hzt t
  unfold heatOp
  rw [hLap]
  simp only [linearOp,hT,zero_mul,Finset.sum_const_zero,sub_zero]

end Yau.F04Proof

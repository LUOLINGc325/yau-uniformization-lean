import Yau.Proofs.C05GradientFlowChartCarrying
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! A continuous loop carried into one genuine convex chart ball is null-homotopic. -/
noncomputable section
open scoped Topology Manifold
namespace Yau.Proofs.C05GradientFlowAux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

theorem loop_nullhomotopic_in_convex_chart {x : M.Carrier} (γ : Path x x)
    (c : M.Carrier) (ε : ℝ) (hε : 0 < ε)
    (hball : Metric.ball (chartPt c c) ε ⊆ chartTarget c)
    (hsource : ∀ u, γ u ∈ (chartAt (ComplexVector n) c).source)
    (himage : ∀ u, chartPt c (γ u) ∈ Metric.ball (chartPt c c) ε) :
    γ.Homotopic (Path.refl x) := by
  classical
  let B := Metric.ball (chartPt c c) ε
  have hx : x ∈ (chartAt (ComplexVector n) c).source := by simpa using hsource 0
  have hxb : chartPt c x ∈ B := by simpa only [γ.source] using himage 0
  let b : B := ⟨chartPt c x, hxb⟩
  have hcoord : Continuous (fun u => chartPt c (γ u)) :=
    (continuousOn_extChartAt (I := ComplexModel n) c).comp_continuous γ.continuous
      (fun u => by simpa only [extChartAt_source] using hsource u)
  let q : Path b b :=
    { toFun := fun u => ⟨chartPt c (γ u), himage u⟩
      continuous_toFun := hcoord.subtype_mk _
      source' := Subtype.ext (by simp [b])
      target' := Subtype.ext (by simp [b]) }
  let ψ : C(B, M.Carrier) :=
    ⟨fun z => chartInv c z, (continuousOn_extChartAt_symm (I := ComplexModel n) c).comp_continuous
      continuous_subtype_val (fun z => hball z.2)⟩
  letI : ContractibleSpace B := (convex_ball (chartPt c c) ε).contractibleSpace
    ⟨chartPt c c, Metric.mem_ball_self hε⟩
  have H := (SimplyConnectedSpace.paths_homotopic q (Path.refl b)).map ψ
  have hbase : ψ b = x := (extChartAt (ComplexModel n) c).left_inv
    (by simpa only [extChartAt_source] using hx)
  have H' := H.pathCast hbase.symm hbase.symm
  convert H' using 1
  · ext u
    exact ((extChartAt (ComplexModel n) c).left_inv
      (by simpa only [extChartAt_source] using hsource u)).symm
  · ext u
    exact hbase.symm

end Yau.Proofs.C05GradientFlowAux

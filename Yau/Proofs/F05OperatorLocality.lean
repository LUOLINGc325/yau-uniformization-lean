import Yau.Geometry.Calculus

/-! The computed Levi matrix and Laplacian are local operators on actual
functions. This also handles patches outside their chart supports. -/

open Set Filter
open scoped Topology ContDiff Manifold
noncomputable section
set_option maxHeartbeats 1800000
namespace Yau.Proofs.F05Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_leviC_locality {f g : ComplexVector n → ℝ} {z : ComplexVector n}
    (hEq : f =ᶠ[𝓝 z] g) : leviC f z = leviC g z := by
  have hComplex : (fun y => (f y : ℂ)) =ᶠ[𝓝 z] (fun y => (g y : ℂ)) :=
    hEq.mono fun y hy => congrArg (fun r : ℝ => (r : ℂ)) hy
  have hD := hComplex.fderiv (𝕜 := ℝ)
  have hBar (a : Fin n) : (fun y => wirtBar (fun q => (f q : ℂ)) y (stdVec a)) =ᶠ[𝓝 z]
      (fun y => wirtBar (fun q => (g q : ℂ)) y (stdVec a)) := by
    filter_upwards [hD] with y hy
    unfold wirtBar
    rw [hy]
  ext a b
  unfold leviC leviMatrix wirt
  rw [(hBar a).fderiv_eq]

theorem F05_laplacian_locality (h : HermitianField M) {f g : M.Carrier → ℝ} {x : M.Carrier}
    (hEq : f =ᶠ[𝓝 x] g) : laplacian h f x = laplacian h g x := by
  have hInvFun : ((chartAt (ComplexVector n) x).symm : ComplexVector n → M.Carrier) = chartInv x := by
    funext z
    simp [chartInv,ComplexModel]
  have hInv : ContinuousAt (chartInv x) (chartPt x x) := by
    rw [← hInvFun]
    simpa [chartPt,ComplexModel] using
      (chartAt (ComplexVector n) x).continuousAt_symm
        ((chartAt (ComplexVector n) x).map_source (mem_chart_source _ x))
  have hCenter : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hTendsto : Tendsto (chartInv x) (𝓝 (chartPt x x)) (𝓝 x) := by
    have hh := hInv.tendsto
    rw [hCenter] at hh
    exact hh
  have hChart : inChart x f =ᶠ[𝓝 (chartPt x x)] inChart x g := hEq.comp_tendsto hTendsto
  unfold laplacian levi
  rw [F05_leviC_locality hChart]

theorem F05_laplacian_zero (h : HermitianField M) (x : M.Carrier) :
    laplacian h (fun _ => 0) x = 0 := by
  have hLevi : levi (fun _ : M.Carrier => 0) x = 0 := by
    ext a b
    simp [levi,leviC,leviMatrix,wirt,wirtBar,inChart]
  rw [laplacian,hLevi]
  simp [traceWith]

theorem F05_laplacian_locally_zero (h : HermitianField M) {f : M.Carrier → ℝ} {x : M.Carrier}
    (hEq : f =ᶠ[𝓝 x] 0) : laplacian h f x = 0 :=
  (F05_laplacian_locality h hEq).trans (F05_laplacian_zero h x)

end Yau.Proofs.F05Aux

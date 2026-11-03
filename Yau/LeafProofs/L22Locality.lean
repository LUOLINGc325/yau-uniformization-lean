import Yau.LeafProofs.L22Basic

noncomputable section

open scoped Topology ContDiff Manifold Matrix ComplexOrder
open Filter

namespace Yau.LeafProofs.L22Aux

theorem leviC_congr_of_eventuallyEq {n : ℕ} {f g : ComplexVector n → ℝ}
    {z : ComplexVector n} (hfg : f =ᶠ[𝓝 z] g) : leviC f z = leviC g z := by
  have hF : (fun y => (f y : ℂ)) =ᶠ[𝓝 z] (fun y => (g y : ℂ)) :=
    hfg.fun_comp Complex.ofReal
  have hdF : fderiv ℝ (fun y => (f y : ℂ)) =ᶠ[𝓝 z]
      fderiv ℝ (fun y => (g y : ℂ)) := hF.fderiv
  ext i j
  have hbar : (fun y => wirtBar (fun x => (f x : ℂ)) y (stdVec i)) =ᶠ[𝓝 z]
      (fun y => wirtBar (fun x => (g x : ℂ)) y (stdVec i)) := by
    filter_upwards [hdF] with y hy
    simp only [wirtBar, hy]
  simp only [leviC, leviMatrix, wirt, hbar.fderiv_eq]

theorem levi_congr_of_eventuallyEq {n : ℕ} {M : ComplexManifold n}
    {f g : M.Carrier → ℝ} {x : M.Carrier} (hfg : f =ᶠ[𝓝 x] g) :
    levi f x = levi g x := by
  have hi : Tendsto (chartInv x) (𝓝 (chartPt x x)) (𝓝 x) := by
    have hc := (continuousAt_extChartAt_symm (I := ComplexModel n) x).tendsto
    change Tendsto (chartInv x) (𝓝 (chartPt x x)) (𝓝 (chartInv x (chartPt x x))) at hc
    have heq : chartInv x (chartPt x x) = x :=
      (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
    rwa [heq] at hc
  exact leviC_congr_of_eventuallyEq (hi.eventually hfg)

end Yau.LeafProofs.L22Aux

import Yau.LeafProofs.L05ChuPatchGeometry

noncomputable section

open Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

local instance l05ChuPatchPlateauDualGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance l05ChuPatchPlateauDualSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance l05ChuPatchPlateauHessianGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance l05ChuPatchPlateauHessianSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

theorem chu_cutoff_spatialDD_on_plateau {n : ℕ} {h : ℝ} (hh : 0 < h)
    (c : Space n) (u : Point n → ℝ) (theta : ℝ → ℝ) {p : Point n}
    (hSpace : ‖p.1-c‖ < h) (hTime : theta p.2=1) :
    spatialDD (fun z : Point n => theta z.2*(L16Aux.innerPatchBump h hh c z.1*u z)) p=spatialDD u p := by
  have hBump : (L16Aux.innerPatchBump h hh c : Space n → ℝ) =ᶠ[𝓝 p.1] (fun _ => 1) := by
    apply (L16Aux.innerPatchBump h hh c).eventuallyEq_one_of_mem_ball
    simpa only [L16Aux.innerPatchBump,Metric.mem_ball,dist_eq_norm] using hSpace
  have hEq : (fun x : Space n => theta p.2*(L16Aux.innerPatchBump h hh c x*u (x,p.2))) =ᶠ[𝓝 p.1]
      (fun x : Space n => u (x,p.2)) := by
    filter_upwards [hBump] with x hx
    rw [hTime,hx,one_mul,one_mul]
  simpa only [spatialDD] using (hEq.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)

theorem chu_near_pair_cutoff_hessian {n : ℕ} {p0 q : Point n} {h : ℝ} (hh : 0 < h)
    (u : Point n → ℝ) (hTime : q.2 ≤ p0.2) (hNear : parabolicDistance q p0 ≤ h/2) :
    let w : Point n → ℝ := fun z => chuCausalTimeCutoff (p0.2-4*h^2) p0.2 z.2*
      (L16Aux.innerPatchBump h hh p0.1 z.1*u z)
    spatialDD w p0=spatialDD u p0 ∧ spatialDD w q=spatialDD u q := by
  dsimp only
  have hl : p0.2-4*h^2 < p0.2 := by nlinarith only [sq_pos_of_pos hh]
  have hq := chu_near_pair_patch_plateau hh hTime hNear
  have hx : ‖q.1-p0.1‖ < h := by
    have hhx : ‖q.1-p0.1‖ ≤ h/2 := (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans hNear
    linarith only [hhx,hh]
  refine ⟨chu_cutoff_spatialDD_on_plateau hh p0.1 u _ (by simpa only [sub_self,norm_zero] using hh)
    (chuCausalTimeCutoff_one_late hl (by nlinarith only [sq_nonneg h])),
    chu_cutoff_spatialDD_on_plateau hh p0.1 u _ hx hq.2.2⟩

end Yau.LeafProofs.L05Aux

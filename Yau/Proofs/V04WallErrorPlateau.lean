import Yau.Proofs.V04CutoffProfiles
import Yau.Proofs.V03WallHessian

/-! Derivative support follows from the actual local plateau of each wall
profile. Pointwise equality of a cutoff alone is never differentiated. -/

open Filter
open scoped Manifold Topology ContDiff Matrix
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem leviMatrix_congr_of_eventuallyEq {f g : E → ℝ} {z : E}
    (heq : f =ᶠ[𝓝 z] g) (dir : ι → E) : leviMatrix f z dir = leviMatrix g z dir := by
  have hC : (fun y => (f y : ℂ)) =ᶠ[𝓝 z] (fun y => (g y : ℂ)) :=
    heq.mono fun _ h => congrArg Complex.ofReal h
  ext a b
  have hbar : (fun y => wirtBar (fun x => (f x : ℂ)) y (dir a)) =ᶠ[𝓝 z]
      (fun y => wirtBar (fun x => (g x : ℂ)) y (dir a)) := by
    filter_upwards [hC.fderiv (𝕜 := ℝ)] with y hy
    simp only [wirtBar, hy]
  simp only [leviMatrix, wirt, hbar.fderiv_eq (𝕜 := ℝ)]

theorem leviMatrix_const (c : ℝ) (z : E) (dir : ι → E) :
    leviMatrix (fun _ => c) z dir = 0 := by
  ext a b
  simp [leviMatrix, wirt, wirtBar, fderiv_const]

variable {n q : ℕ} {X : KahlerManifold n}

theorem baseWall_eq_zero_near {d : VariationData X q} (hd : VariationSetup d)
    (C : ℕ → ℝ) (j : ℕ) (x : Pt X)
    (hcut : clockBaseCutoff d (chosenClockData X C) j x ≠ 1) :
    (inChart x (wallBase d j)) =ᶠ[𝓝 (chartPt x x)] (fun _ => 0) := by
  have hlt : baseClockProfile (d.u x / d.A j) < 1 :=
    lt_of_le_of_ne (baseClockProfile_bounds _).2 hcut
  obtain ⟨V, hV, hxV, hprofile⟩ := base_wall_profile_constant_near (setup_wallProfiles hd) hlt
  have hround : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hu : ContinuousAt (fun z => d.u (chartInv x z) / d.A j) (chartPt x x) :=
    (((hd.2.2.2.1.1 x).continuousOn.continuousAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
        (mem_extChartAt_target x))).div_const _)
  have hv : ∀ᶠ z in 𝓝 (chartPt x x), d.u (chartInv x z) / d.A j ∈ V := by
    apply hu.eventually
    change V ∈ 𝓝 (d.u (chartInv x (chartPt x x)) / d.A j)
    rw [hround]
    exact hV.mem_nhds hxV
  filter_upwards [hv] with z hz
  simp only [inChart, wallBase, deltaBase, hprofile _ hz, inv_one, sub_self]

theorem baseWall_laplacian_eq_zero_of_cutoff_ne_one
    {d : VariationData X q} (hd : VariationSetup d) (C : ℕ → ℝ)
    (j : ℕ) (x : Pt X) (h : HermitianField X.manifold)
    (hcut : clockBaseCutoff d (chosenClockData X C) j x ≠ 1) :
    laplacian h (wallBase d j) x = 0 := by
  have heq := leviMatrix_congr_of_eventuallyEq (baseWall_eq_zero_near hd C j x hcut) stdVec
  rw [leviMatrix_const] at heq
  simp only [laplacian, levi, leviC, heq, traceWith, Matrix.mul_zero, Matrix.trace_zero,
    Complex.zero_re]

end Yau.Blueprint.V04Proof.WallErrorAux

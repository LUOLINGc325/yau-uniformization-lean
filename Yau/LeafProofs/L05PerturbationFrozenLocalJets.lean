import Yau.LeafProofs.L05PerturbationFrozenPatchJets
import Yau.LeafProofs.L05PerturbationLocalC2Cover

open Filter Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_frozen_core_patch_of_autonomous {n : ℕ} {ell L eta0 C0 : ℝ}
    (hAuto : ∀ F : Sym n → ℝ, Continuous F → globalElliptic F ell L →
      ConcaveOn ℝ univ F → F 0=0 → ∀ v : Point n → ℝ, ContinuousOn v (unitClosed n) →
      (∀ p∈unitClosed n, |v p| ≤ 1) →
      viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) v →
      SchauderBound eta0 (backward (1/2)) v C0)
    {F : Sym n → ℝ} (hF : Continuous F) (hE : globalElliptic F ell L)
    (hConc : ConcaveOn ℝ univ F) (h0 : F 0=0) {h : Point n → ℝ}
    (hC : ContinuousOn h (perturbClosed (0 : Space n) (1/2) 0))
    (hSup : ∀ p∈perturbClosed (0 : Space n) (1/2) 0, |h p| ≤ 1)
    (hSol : viscositySolution (perturbOpen (0 : Space n) (1/2) 0)
      (fun H _ => F H) (fun _ => 0) h)
    {tau : ℝ} (ht : 0 < tau) (htb : tau ≤ 1/8) {p : Point n} (hp : p∈perturbCore tau) :
    ∃ V P : Set (Point n), IsOpen V ∧ p∈V ∧ perturbCore tau∩V⊆P ∧ C2 P h ∧
      ‖hessian h p‖ ≤ (1+4*(Fintype.card (RIdx n) : ℝ)*C0)*tau^(-2 : ℝ) ∧
      timeD (perturbCore tau) h p=F (hessian h p) := by
  let z := perturbCorePatchCenter p tau
  let r := tau/2
  have hr : 0 < r := by dsimp only [r]; positivity
  have hRadius : r/2=tau/4 := by dsimp only [r]; ring
  have hBuf : perturbClosed z.1 r z.2 ⊆ perturbBack (0 : Space n) (1/2) 0 :=
    perturb_core_patch_closed_subset ht hp
  have hPatch := perturb_frozen_patch_jets_of_autonomous hAuto hr z hBuf hF hE hConc h0 hC hSup hSol
  have hpPatch : p∈perturbBack z.1 (r/2) z.2 := by
    rw [hRadius]
    exact perturb_core_point_in_half_patch ht hp
  have hTop : p.2 < z.2 ∨ z.2=0 := perturb_core_point_time_interior_or_top ht hp
  obtain ⟨V,hV,hpV,hSub⟩ := perturb_back_relative_neighborhood
    (Q := perturbCore tau) (fun q hq => hq.2.2) hpPatch hTop
  have hScale : (r⁻¹)^2*((Fintype.card (RIdx n) : ℝ)*C0)=
      (4*(Fintype.card (RIdx n) : ℝ)*C0)*tau^(-2 : ℝ) := by
    dsimp only [r]
    rw [Real.rpow_neg ht.le,Real.rpow_two]
    field_simp [ht.ne'] <;> ring
  have hMat : ‖hessian h p‖ ≤ (1+4*(Fintype.card (RIdx n) : ℝ)*C0)*tau^(-2 : ℝ) := by
    have hh := hPatch.2.1 p hpPatch
    rw [hScale] at hh
    nlinarith only [hh,Real.rpow_nonneg ht.le (-2 : ℝ)]
  have hTime := perturb_timeD_of_relative_patch hPatch.1 hV hSub hp hpV (perturb_core_uniqueDiff ht.le htb hp)
  exact ⟨V,perturbBack z.1 (r/2) z.2,hV,hpV,hSub,hPatch.1,hMat,hTime.trans (hPatch.2.2 p hpPatch)⟩

theorem perturb_frozen_core_jets_from_witness {n : ℕ} {ell L eta0 C0 : ℝ} (hC0 : 0 < C0)
    (hAuto : ∀ F : Sym n → ℝ, Continuous F → globalElliptic F ell L →
      ConcaveOn ℝ univ F → F 0=0 → ∀ v : Point n → ℝ, ContinuousOn v (unitClosed n) →
      (∀ p∈unitClosed n, |v p| ≤ 1) →
      viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) v →
      SchauderBound eta0 (backward (1/2)) v C0) :
    ∃ Kh : ℝ, 0 < Kh ∧ ∀ (F : Sym n → ℝ) (h : Point n → ℝ),
      Continuous F → globalElliptic F ell L → ConcaveOn ℝ univ F → F 0=0 →
      ContinuousOn h (perturbClosed (0 : Space n) (1/2) 0) →
      (∀ p∈perturbClosed (0 : Space n) (1/2) 0, |h p| ≤ 1) →
      viscositySolution (perturbOpen (0 : Space n) (1/2) 0) (fun H _ => F H) (fun _ => 0) h →
      ∀ tau : ℝ, 0 < tau → tau ≤ 1/8 →
        C2 (perturbCore tau) h ∧
        (∀ p∈perturbCore tau, ‖hessian h p‖ ≤ Kh*tau^(-2 : ℝ)) ∧
        ∀ p∈perturbCore tau, timeD (perturbCore tau) h p=F (hessian h p) := by
  let Kh := 1+4*(Fintype.card (RIdx n) : ℝ)*C0
  have hKh : 0 < Kh := by dsimp only [Kh]; positivity
  refine ⟨Kh,hKh,?_⟩
  intro F h hF hE hConc h0 hC hSup hSol tau ht htb
  have hLocal := fun p (hp : p∈perturbCore (n := n) tau) =>
    perturb_frozen_core_patch_of_autonomous hAuto hF hE hConc h0 hC hSup hSol ht htb hp
  refine ⟨perturb_c2_of_relative_cover (fun p hp => perturb_core_uniqueDiff ht.le htb hp) ?_,?_,?_⟩
  · intro p hp
    obtain ⟨V,P,hV,hpV,hSub,hC2,_,_⟩ := hLocal p hp
    exact ⟨V,P,hV,hpV,hSub,hC2⟩
  · intro p hp
    obtain ⟨_,_,_,_,_,_,hMat,_⟩ := hLocal p hp
    exact hMat
  · intro p hp
    obtain ⟨_,_,_,_,_,_,_,hTime⟩ := hLocal p hp
    exact hTime

end Yau.LeafProofs.L05Aux

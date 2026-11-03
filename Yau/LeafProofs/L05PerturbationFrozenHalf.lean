import Yau.LeafProofs.L05PerturbationOperatorScaling
import Yau.LeafProofs.L05PerturbationViscosityTransport
import Yau.LeafProofs.L05PerturbationTimeTransport
import Yau.LeafProofs.L05FrozenDirichlet

open Filter MeasureTheory Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def perturbFrozenScale {n : ℕ} (F : Sym n → ℝ) (H : Sym n) : ℝ := (1/4)*F ((4 : ℝ) • H)

theorem perturb_frozenScale_eq {n : ℕ} {F : Sym n → ℝ} (h0 : F 0=0) :
    perturbFrozenScale F=perturbOperatorScale F 0 4 := by
  funext H
  simp only [perturbFrozenScale,perturbOperatorScale,zero_add,h0,sub_zero]
  ring

theorem perturb_half_scale_mem {n : ℕ} {p : Point n} (hp : p∈unitClosed n) :
    perturbScale (1/2) p∈perturbClosed (0 : Space n) (1/2) 0 := by
  have hP : p∈perturbClosed (0 : Space n) 1 0 := by
    simpa only [unitClosed,Yau.Parabolic.cylinder,perturbClosed,one_pow,zero_sub] using hp
  have hh := perturb_center_mem_closed (0 : Point n) (by norm_num : (0 : ℝ) < 1/2) hP
  simpa only [perturbCenter,perturbScale,Prod.fst_zero,Prod.snd_zero,zero_add] using hh

theorem perturb_twice_scale_closed {n : ℕ} {p : Point n}
    (hp : p∈perturbClosed (0 : Space n) (1/2) 0) : perturbScale 2 p∈unitClosed n := by
  have hx : ‖p.1‖ ≤ 1/2 := by simpa only [mem_closedBall,dist_zero_right] using hp.1
  have ht : -(1/2 : ℝ)^2 ≤ p.2 := by simpa only [zero_sub] using hp.2.1
  refine ⟨?_,?_,?_⟩
  · change dist ((2 : ℝ) • p.1) 0 ≤ 1
    rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  · change (-1 : ℝ) ≤ (2 : ℝ)^2*p.2
    linarith
  · change (2 : ℝ)^2*p.2 ≤ 0
    linarith [hp.2.2]

theorem perturb_twice_scale_open {n : ℕ} {p : Point n}
    (hp : p∈perturbOpen (0 : Space n) (1/2) 0) : perturbScale 2 p∈unitOpen n := by
  have hx : ‖p.1‖ < 1/2 := by simpa only [mem_ball,dist_zero_right] using hp.1
  have ht : -(1/2 : ℝ)^2 < p.2 := by simpa only [zero_sub] using hp.2.1
  refine ⟨?_,?_,?_⟩
  · change dist ((2 : ℝ) • p.1) 0 < 1
    rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  · change (-1 : ℝ) < (2 : ℝ)^2*p.2
    linarith
  · change (2 : ℝ)^2*p.2 < 0
    linarith [hp.2.2]

theorem perturb_twice_scale_boundary {n : ℕ} {p : Point n}
    (hp : p∈perturbBoundary (0 : Space n) (1/2) 0) :
    perturbScale 2 p∈parabolicBoundary n := by
  have hc := perturb_twice_scale_closed (perturbBoundary_subset_closed 0 (1/2) 0 hp)
  rcases hp with hp | hp
  · left
    refine ⟨hc.1,?_⟩
    have ht : p.2=0-(1/2 : ℝ)^2 := mem_singleton_iff.mp hp.2
    change (2 : ℝ)^2*p.2=(-1 : ℝ)
    rw [ht]
    norm_num
  · right
    refine ⟨?_,hc.2⟩
    have hx : ‖p.1‖=1/2 := by simpa only [mem_sphere,dist_zero_right] using hp.1
    change dist ((2 : ℝ) • p.1) 0=1
    rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ) < 2),hx]
    norm_num

theorem perturb_scale_two_affine {n : ℕ} (p : Point n) :
    harnackAffine (0 : Space n) 2 (-4) 4 p=perturbScale 2 p := by
  rw [harnack_affine_apply]
  apply Prod.ext
  · simp only [perturbScale,zero_add]
  · change -4+4*(p.2+1)=(2 : ℝ)^2*p.2
    ring

theorem perturb_frozen_half_exists {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) {F : Sym n → ℝ}
    (hF : Continuous F) (hE : globalElliptic F ell L) (hConc : ConcaveOn ℝ univ F)
    (h0 : F 0=0) {u : Point n → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hu : ContinuousOn u (perturbClosed (0 : Space n) (1/2) 0))
    (hBound : ∀ p∈perturbClosed (0 : Space n) (1/2) 0, |u p| ≤ B) :
    ∃ h : Point n → ℝ, ContinuousOn h (perturbClosed (0 : Space n) (1/2) 0) ∧
      EqOn h u (perturbBoundary (0 : Space n) (1/2) 0) ∧
      viscositySolution (perturbOpen (0 : Space n) (1/2) 0) (fun H _ => F H) (fun _ => 0) h ∧
      ∀ p∈perturbClosed (0 : Space n) (1/2) 0, |h p| ≤ B := by
  let G := perturbFrozenScale F
  let g : Point n → ℝ := fun p => u (perturbScale (1/2) p)
  have hG : Continuous G := by
    rw [show G=perturbOperatorScale F 0 4 from perturb_frozenScale_eq h0]
    exact perturb_operatorScale_continuous hF _ _
  have hGE : globalElliptic G ell L := by
    rw [show G=perturbOperatorScale F 0 4 from perturb_frozenScale_eq h0]
    exact perturb_operatorScale_elliptic hE (by norm_num) _
  have hGC : ConcaveOn ℝ univ G := by
    rw [show G=perturbOperatorScale F 0 4 from perturb_frozenScale_eq h0]
    exact perturb_operatorScale_concave hConc (by norm_num) _
  have hG0 : G 0=0 := by simp [G,perturbFrozenScale,h0]
  have hg : ContinuousOn g (unitClosed n) :=
    hu.comp (perturbScale_continuous (1/2)).continuousOn (fun _ hp => perturb_half_scale_mem hp)
  obtain ⟨v,hv,hEq,hSol,hVbound⟩ := frozenBellmanDirichletGap_proved n hn ell L hell hL G hG hGE
    hGC hG0 g B hB hg (fun p hp => hBound _ (perturb_half_scale_mem hp))
  let h : Point n → ℝ := fun p => v (perturbScale 2 p)
  have hMap : MapsTo (harnackAffine (0 : Space n) 2 (-4) 4)
      (perturbOpen (0 : Space n) (1/2) 0) (unitOpen n) := by
    intro p hp
    rw [perturb_scale_two_affine]
    exact perturb_twice_scale_open hp
  have hSub := perturb_viscosity_sub_affine hSol.1 (0 : Space n) (R := 2) (a := -4)
    (T := 4) (N := 1) (by norm_num) (by norm_num) (by norm_num) hMap
  have hSuper := perturb_viscosity_super_affine hSol.2 (0 : Space n) (R := 2) (a := -4)
    (T := 4) (N := 1) (by norm_num) (by norm_num) (by norm_num) hMap
  have hRecover (H : Sym n) : (4 : ℝ)*G ((1*((2 : ℝ)⁻¹)^2) • H)=F H := by
    dsimp only [G,perturbFrozenScale]
    norm_num [smul_smul]
    ring
  refine ⟨h,hv.comp (perturbScale_continuous 2).continuousOn
    (fun _ hp => perturb_twice_scale_closed hp),?_,?_,?_⟩
  · intro p hp
    change v (perturbScale 2 p)=u p
    rw [hEq (perturb_twice_scale_boundary hp)]
    dsimp only [g]
    rw [perturbScale_comp]
    norm_num
    exact congrArg u (perturbScale_one p)
  · constructor
    · simpa only [div_one,mul_zero,hRecover,perturb_scale_two_affine] using hSub
    · simpa only [div_one,mul_zero,hRecover,perturb_scale_two_affine] using hSuper
  · intro p hp
    exact hVbound _ (perturb_twice_scale_closed hp)

end Yau.LeafProofs.L05Aux

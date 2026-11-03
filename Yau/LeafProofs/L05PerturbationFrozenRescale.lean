import Yau.LeafProofs.L05PerturbationFrozenHalf

open Filter Set Metric
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def perturbFrozenRescale {n : ℕ} (F : Sym n → ℝ) (r : ℝ) : Sym n → ℝ :=
  perturbOperatorScale F 0 ((r⁻¹)^2)

theorem perturb_frozen_rescale_eq {n : ℕ} {r : ℝ} (hr : 0 < r)
    (F : Sym n → ℝ) (h0 : F 0=0) (H : Sym n) :
    perturbFrozenRescale F r H=r^2*F ((r⁻¹)^2 • H) := by
  simp only [perturbFrozenRescale,perturbOperatorScale,zero_add,h0,sub_zero]
  field_simp [hr.ne']

theorem perturb_frozen_rescale_data {n : ℕ} {r ell L : ℝ} (hr : 0 < r)
    {F : Sym n → ℝ} (hF : Continuous F) (hE : globalElliptic F ell L)
    (hConc : ConcaveOn ℝ univ F) :
    Continuous (perturbFrozenRescale F r) ∧ globalElliptic (perturbFrozenRescale F r) ell L ∧
      ConcaveOn ℝ univ (perturbFrozenRescale F r) ∧ perturbFrozenRescale F r 0=0 :=
  ⟨perturb_operatorScale_continuous hF 0 _,
    perturb_operatorScale_elliptic hE (sq_pos_of_pos (inv_pos.mpr hr)) 0,
    perturb_operatorScale_concave hConc (sq_pos_of_pos (inv_pos.mpr hr)) 0,
    perturb_operatorScale_zero F 0 _⟩

theorem perturb_unit_center_mem_closed {n : ℕ} (z : Point n) {r : ℝ} (hr : 0 < r)
    {p : Point n} (hp : p∈unitClosed n) : perturbCenter z r p∈perturbClosed z.1 r z.2 := by
  have hP : p∈perturbClosed (0 : Space n) 1 0 := by
    simpa only [unitClosed,Yau.Parabolic.cylinder,perturbClosed,one_pow,zero_sub] using hp
  exact perturb_center_mem_closed z hr hP

theorem perturb_frozen_patch_data {n : ℕ} {r : ℝ} (hr : 0 < r) (z : Point n)
    (hBuf : perturbClosed z.1 r z.2 ⊆ perturbBack (0 : Space n) (1/2) 0)
    {F : Sym n → ℝ} (h0 : F 0=0) {h : Point n → ℝ}
    (hC : ContinuousOn h (perturbClosed (0 : Space n) (1/2) 0))
    (hSup : ∀ p∈perturbClosed (0 : Space n) (1/2) 0, |h p| ≤ 1)
    (hSol : viscositySolution (perturbOpen (0 : Space n) (1/2) 0)
      (fun H _ => F H) (fun _ => 0) h) :
    ContinuousOn (fun p => h (perturbCenter z r p)) (unitClosed n) ∧
      (∀ p∈unitClosed n, |h (perturbCenter z r p)| ≤ 1) ∧
      viscositySolution (unitOpen n) (fun H _ => perturbFrozenRescale F r H) (fun _ => 0)
        (fun p => h (perturbCenter z r p)) := by
  have hMapClosed : MapsTo (perturbCenter z r) (unitClosed n) (perturbClosed (0 : Space n) (1/2) 0) :=
    fun p hp => perturbBack_subset_closed _ _ _ (hBuf (perturb_unit_center_mem_closed z hr hp))
  have hTop : z.2 ≤ 0 :=
    (hBuf ⟨mem_closedBall_self hr.le,sub_le_self z.2 (sq_nonneg _),le_rfl⟩).2.2
  have hMapOpen : MapsTo (harnackAffine z.1 r (z.2-r^2) (r^2)) (unitOpen n)
      (perturbOpen (0 : Space n) (1/2) 0) := by
    intro p hp
    rw [perturb_harnack_center]
    have hpBack := hBuf (perturb_unit_center_mem_closed z hr (unitOpen_subset_unitClosed hp))
    refine ⟨hpBack.1,hpBack.2.1,?_⟩
    have hpT : p.2 < 0 := hp.2.2
    change z.2+r^2*p.2 < 0
    nlinarith only [hTop,hpT,sq_pos_of_pos hr]
  have hSub := perturb_viscosity_sub_affine hSol.1 z.1 (R := r) (a := z.2-r^2) (T := r^2)
    (N := 1) hr (sq_pos_of_pos hr) (by norm_num) hMapOpen
  have hSuper := perturb_viscosity_super_affine hSol.2 z.1 (R := r) (a := z.2-r^2) (T := r^2)
    (N := 1) hr (sq_pos_of_pos hr) (by norm_num) hMapOpen
  have hOp (H : Sym n) : r^2*F ((r⁻¹)^2 • H)=perturbFrozenRescale F r H :=
    (perturb_frozen_rescale_eq hr F h0 H).symm
  refine ⟨hC.comp (perturbCenter_continuous z r).continuousOn hMapClosed,
    fun p hp => hSup _ (hMapClosed hp),?_,?_⟩
  · simpa only [div_one,one_mul,mul_zero,hOp,perturb_harnack_center] using hSub
  · simpa only [div_one,one_mul,mul_zero,hOp,perturb_harnack_center] using hSuper

end Yau.LeafProofs.L05Aux

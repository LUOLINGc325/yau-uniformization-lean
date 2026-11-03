import Yau.LeafProofs.L05PucciHarnackDensity
import Yau.LeafProofs.L05PucciHarnackParabolicGeometry

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem harnack_relative_level_measurable {n : ℕ} {S D : Set (Point n)}
    (hD : IsClosed D) {u : Point n → ℝ} (hu : ContinuousOn u D)
    (hS : MeasurableSet S) (hSD : S ⊆ D) (M : ℝ) :
    MeasurableSet (S ∩ {z | u z ≤ M}) ∧ MeasurableSet (S ∩ {z | M < u z}) := by
  have hClosedLo : IsClosed (D ∩ {z | u z ≤ M}) :=
    hu.preimage_isClosed_of_isClosed hD isClosed_Iic
  have hLoEq : S ∩ {z | u z ≤ M}=S ∩ (D ∩ {z | u z ≤ M}) := by
    ext p
    constructor
    · rintro ⟨hp,hp'⟩
      exact ⟨hp,hSD hp,hp'⟩
    · rintro ⟨hp,_,hp'⟩
      exact ⟨hp,hp'⟩
  have hLo : MeasurableSet (S ∩ {z | u z ≤ M}) := by
    rw [hLoEq]
    exact hS.inter hClosedLo.measurableSet
  refine ⟨hLo,?_⟩
  have hHiEq : S ∩ {z | M < u z}=S\(S ∩ {z | u z ≤ M}) := by
    ext p
    simp only [mem_inter_iff,mem_ofPred_eq,Set.mem_sdiff]
    constructor
    · rintro ⟨hp,hp'⟩
      exact ⟨hp,fun h => not_lt_of_ge h.2 hp'⟩
    · rintro ⟨hp,hNot⟩
      exact ⟨hp,lt_of_not_ge (fun h => hNot ⟨hp,h⟩)⟩
  rw [hHiEq]
  exact hS.diff hLo

theorem harnack_cube_density_forward
    {n : ℕ} {ell L : ℝ} (hell : 0 < ell) (hL : ell ≤ L)
    {u : Point n → ℝ} (hu : harnackSuper0 ell L u)
    {c : Space n} {r a H : ℝ} (hr : 0 < r) (hH : 0 < H)
    (hclosed : harnackClosed c (harnackLocalRadius n*r) a (2*r^2) ⊆ unitClosed n)
    (hopen : harnackOpen c (harnackLocalRadius n*r) a (2*r^2) ⊆ unitOpen n)
    (hdense : (1-harnackDelta n ell L)*harnackMu (harnackBox c r a) <
      harnackMu (harnackBox c r a ∩ {z | harnackLocalM n ell L*H < u z})) :
    ∀ z∈Metric.closedBall c (2*Real.sqrt (2*n)*r) ×ˢ Icc (a+r^2) (a+2*r^2), H < u z := by
  let F := harnackAffine c r (a-r^2) (r^2)
  let U := fun z => u (F z)/H
  have hr2 := sq_pos_of_ne_zero hr.ne'
  have hMap : MapsTo F (harnackClosed 0 (harnackLocalRadius n) 0 2) (unitClosed n) := by
    intro z hz
    apply hclosed
    have h := (harnack_parabolic_closed_mem_iff (a := a) c hr (harnackLocalRadius n) 0 2 z).mpr hz
    simpa only [mul_zero,add_zero,mul_comm] using h
  have hMapOpen : MapsTo F (harnackOpen 0 (harnackLocalRadius n) 0 2) (unitOpen n) := by
    intro z hz
    apply hopen
    have h := (harnack_parabolic_open_mem_iff (a := a) c hr (harnackLocalRadius n) 0 2 z).mpr hz
    simpa only [mul_zero,add_zero,mul_comm] using h
  have hPull := harnack_super_affine_pullback hell.le hL hu.2.2 c
    (a := a-r^2) hr hr2 hH hMapOpen
  simp only [div_self hr2.ne',one_mul,mul_zero] at hPull
  have hU : ContinuousOn U (harnackClosed 0 (harnackLocalRadius n) 0 2) ∧
      (∀ z∈harnackClosed 0 (harnackLocalRadius n) 0 2, 0 ≤ U z) ∧
      viscositySuper (harnackOpen 0 (harnackLocalRadius n) 0 2)
        (fun A _ => harnackPucciMinus ell L A) (fun _ => 0) U :=
    ⟨(hu.1.comp (harnack_affine_contDiff c r (a-r^2) (r^2)).continuous.continuousOn hMap).div_const H,
      fun z hz => div_nonneg (hu.2.1 _ (hMap hz)) hH.le,hPull⟩
  have hBox : harnackBox c r a ⊆ unitClosed n := by
    intro p hp
    let z := harnackAffineInv c r (a-r^2) (r^2) p
    have hFz : F z=p := harnack_affine_apply_inv hr.ne' hr2.ne' p
    have hz : z∈harnackBox (0 : Space n) 1 0 := by
      rw [← harnack_box_affine_preimage (a := a) c hr]
      change F z∈harnackBox c r a
      rwa [hFz]
    have hMapped := hMap (harnack_local_box_subset_closed n hz)
    rwa [hFz] at hMapped
  have hE : MeasurableSet (harnackBox c r a ∩ {z | harnackLocalM n ell L*H < u z}) :=
    (harnack_relative_level_measurable (Metric.isClosed_closedBall.prod isClosed_Icc) hu.1
      (harnack_box_measurable c r a) hBox _).2
  have hPre : F ⁻¹' (harnackBox c r a ∩ {z | harnackLocalM n ell L*H < u z})=
      harnackBox (0 : Space n) 1 0 ∩ {z | harnackLocalM n ell L < U z} := by
    change harnackAffine c r (a-r^2) (r^2) ⁻¹' _=_
    rw [preimage_inter,harnack_box_affine_preimage (a := a) c hr]
    ext z
    simp only [mem_inter_iff,mem_preimage,mem_ofPred_eq,U,F,lt_div_iff₀ hH]
  have hMu := harnack_mu_affine_preimage (a := a-r^2) c hr hr2 hE
  change harnackMu _=harnackAffineJacobian n r (r^2)*harnackMu (F ⁻¹' _) at hMu
  rw [hPre] at hMu
  have hJac : harnackAffineJacobian n r (r^2)=r^(2*n+2) := by
    rw [harnackAffineJacobian,pow_add]
  rw [harnack_box_mu c hr,hMu,hJac] at hdense
  have hDensRef : (1-harnackDelta n ell L)*harnackCubeVolume n <
      harnackMu (harnackBox (0 : Space n) 1 0 ∩ {z | harnackLocalM n ell L < U z}) := by
    apply (mul_lt_mul_iff_of_pos_left (pow_pos hr (2*n+2))).mp
    nlinarith only [hdense]
  have hRef := harnack_reference_cube_density hell hL hU hDensRef
  intro p hp
  let z := harnackAffineInv c r (a-r^2) (r^2) p
  have hFz : F z=p := harnack_affine_apply_inv hr.ne' hr2.ne' p
  have hz : z∈Metric.closedBall (0 : Space n) (2*Real.sqrt (2*n)) ×ˢ Icc (1 : ℝ) 2 := by
    have hPhysical : F z∈harnackClosed c (r*(2*Real.sqrt (2*n))) (a+r^2*1) (r^2*1) := by
      rw [hFz]
      have ht : a+r^2+r^2=a+2*r^2 := by ring
      simpa only [harnackClosed,mul_one,mul_comm,ht] using hp
    have hz' := (harnack_parabolic_closed_mem_iff (a := a) c hr (2*Real.sqrt (2*n)) 1 1 z).mp hPhysical
    simpa only [harnackClosed,show (1 : ℝ)+1=2 by norm_num] using hz'
  have hPoint := hRef z hz
  change 1 < u (F z)/H at hPoint
  rw [hFz] at hPoint
  simpa only [one_mul] using (lt_div_iff₀ hH).mp hPoint

end Yau.LeafProofs.L05Aux

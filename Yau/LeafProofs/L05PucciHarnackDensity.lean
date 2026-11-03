import Yau.LeafProofs.L05PucciHarnackCube
import Yau.LeafProofs.L05PucciHarnackLocalBarrier
import Yau.LeafProofs.L05PucciHarnackSlabs

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem harnack_local_box_subset_closed (n : ℕ) :
    harnackBox (0 : Space n) 1 0 ⊆ harnackClosed 0 (harnackLocalRadius n) 0 2 := by
  intro p hp
  have hx := harnack_cube_subset_closedBall (0 : Space n) (by norm_num : (0 : ℝ) ≤ 1) hp.1
  have hSmall : Real.sqrt (2*n)*1/2 ≤ 2*Real.sqrt (2*n) := by
    nlinarith [Real.sqrt_nonneg (2*n)]
  have hx' := Metric.closedBall_subset_closedBall hSmall hx
  have hModel : (p.1,(1 : ℝ))∈Metric.closedBall (0 : Space n) (2*Real.sqrt (2*n)) ×ˢ Icc (1 : ℝ) 2 :=
    ⟨hx',le_rfl,by norm_num⟩
  have hCyl := harnack_local_target_subset_closed n hModel
  exact ⟨hCyl.1,by linarith [hp.2.1],by norm_num at hp ⊢; linarith [hp.2.2]⟩

theorem harnack_localForcingSet_subset_box (n : ℕ) :
    harnackLocalForcingSet n ⊆ harnackBox (0 : Space n) 1 0 := by
  intro p hp
  have hr : Real.sqrt (3/128) < (1 : ℝ)/2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3/128)
    nlinarith [Real.sqrt_nonneg (3/128)]
  refine ⟨harnack_cube_contains_ball 0 (Metric.closedBall_subset_ball hr hp.1),?_,?_⟩
  · exact lt_of_lt_of_le (harnack_localEpsilon_pos n) hp.2.1
  · have h := harnack_localEpsilon_small n
    change p.2 ≤ 0+1^2
    linarith [hp.2.2]

def harnackDelta (n : ℕ) (ell L : ℝ) : ℝ :=
  min (1/4) (harnackLocalJ n ell L/(2*harnackCubeVolume n))

theorem harnack_delta_pos {n : ℕ} {ell L : ℝ} (hell : 0 < ell) :
    0 < harnackDelta n ell L :=
  lt_min (by norm_num) (div_pos (harnack_localJ_pos hell) (mul_pos (by norm_num) (harnack_cubeVolume_pos n)))

theorem harnack_delta_le_quarter (n : ℕ) (ell L : ℝ) :
    harnackDelta n ell L ≤ 1/4 := min_le_left _ _

theorem harnack_delta_volume_le (n : ℕ) (ell L : ℝ) :
    2*harnackDelta n ell L*harnackCubeVolume n ≤ harnackLocalJ n ell L := by
  have h := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (harnack_cubeVolume_pos n))).mp
    (min_le_right (1/4 : ℝ) (harnackLocalJ n ell L/(2*harnackCubeVolume n)))
  change harnackDelta n ell L*(2*harnackCubeVolume n) ≤ _ at h
  nlinarith only [h]

theorem harnack_reference_cube_density {n : ℕ} {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) {u : Point n → ℝ}
    (hu : ContinuousOn u (harnackClosed 0 (harnackLocalRadius n) 0 2) ∧
      (∀ z∈harnackClosed 0 (harnackLocalRadius n) 0 2, 0 ≤ u z) ∧
      viscositySuper (harnackOpen 0 (harnackLocalRadius n) 0 2)
        (fun H _ => harnackPucciMinus ell L H) (fun _ => 0) u)
    (hdense : (1-harnackDelta n ell L)*harnackCubeVolume n <
      harnackMu (harnackBox (0 : Space n) 1 0 ∩ {z | harnackLocalM n ell L < u z})) :
    ∀ z∈Metric.closedBall (0 : Space n) (2*Real.sqrt (2*n)) ×ˢ Icc (1 : ℝ) 2, 1 < u z := by
  intro z hz
  by_contra hNot
  have hLow := harnack_reference_local_low_measure hell hL hu ⟨z,hz,le_of_not_gt hNot⟩
  let B := harnackBox (0 : Space n) 1 0
  let Lo := B ∩ {z | u z ≤ harnackLocalM n ell L}
  let Hi := B ∩ {z | harnackLocalM n ell L < u z}
  have hClosedLo : IsClosed (harnackClosed 0 (harnackLocalRadius n) 0 2 ∩
      {z | u z ≤ harnackLocalM n ell L}) :=
    hu.1.preimage_isClosed_of_isClosed (Metric.isClosed_closedBall.prod isClosed_Icc) isClosed_Iic
  have hLoEq : Lo=B ∩ (harnackClosed 0 (harnackLocalRadius n) 0 2 ∩
      {z | u z ≤ harnackLocalM n ell L}) := by
    ext p
    constructor
    · rintro ⟨hp,hp'⟩
      exact ⟨hp,harnack_local_box_subset_closed n hp,hp'⟩
    · rintro ⟨hp,_,hp'⟩
      exact ⟨hp,hp'⟩
  have hLoMeas : MeasurableSet Lo := by
    rw [hLoEq]
    exact (harnack_box_measurable 0 1 0).inter hClosedLo.measurableSet
  have hHiEq : Hi=B\Lo := by
    ext p
    simp only [Hi,Lo,mem_inter_iff,mem_ofPred_eq,Set.mem_sdiff]
    constructor
    · rintro ⟨hp,hlt⟩
      exact ⟨hp,fun h => not_lt_of_ge h.2 hlt⟩
    · rintro ⟨hp,hNot⟩
      exact ⟨hp,lt_of_not_ge (fun h => hNot ⟨hp,h⟩)⟩
  have hHiMeas : MeasurableSet Hi := hHiEq ▸ (harnack_box_measurable 0 1 0).diff hLoMeas
  have hLoFin : (volume : Measure (Point n)) Lo≠⊤ :=
    ne_top_of_le_ne_top (harnack_box_measure_ne_top 0 (by norm_num) 0) (measure_mono inter_subset_left)
  have hHiFin : (volume : Measure (Point n)) Hi≠⊤ :=
    ne_top_of_le_ne_top (harnack_box_measure_ne_top 0 (by norm_num) 0) (measure_mono inter_subset_left)
  have hUnion : Lo∪Hi=B := by
    ext p
    constructor
    · intro h
      exact h.elim And.left And.left
    · intro hp
      by_cases hu : u p ≤ harnackLocalM n ell L
      · exact Or.inl ⟨hp,hu⟩
      · exact Or.inr ⟨hp,lt_of_not_ge hu⟩
  have hDisjoint : Disjoint Lo Hi := by
    rw [disjoint_left]
    rintro p ⟨_,hp⟩ ⟨_,hp'⟩
    change u p ≤ harnackLocalM n ell L at hp
    change harnackLocalM n ell L < u p at hp'
    exact not_lt_of_ge hp hp'
  have hSum : harnackMu Lo+harnackMu Hi=harnackCubeVolume n := by
    have h := measureReal_union (μ := (volume : Measure (Point n))) hDisjoint hHiMeas hLoFin hHiFin
    rw [hUnion] at h
    have hB : harnackMu B=harnackCubeVolume n := by
      simpa only [B,one_pow,mul_one] using harnack_box_mu (0 : Space n) (by norm_num : (0 : ℝ) < 1) 0
    change harnackMu B=harnackMu Lo+harnackMu Hi at h
    exact h.symm.trans hB
  have hLoLower : harnackLocalJ n ell L ≤ harnackMu Lo := hLow.trans
    (harnack_mu_mono hLoFin (fun p hp => ⟨harnack_localForcingSet_subset_box n hp.1,hp.2⟩))
  have hDelta := harnack_delta_volume_le n ell L
  have hDpos := harnack_delta_pos (n := n) (L := L) hell
  have hVpos := harnack_cubeVolume_pos n
  change (1-harnackDelta n ell L)*harnackCubeVolume n < harnackMu Hi at hdense
  nlinarith

end Yau.LeafProofs.L05Aux

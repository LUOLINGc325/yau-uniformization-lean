import Yau.LeafProofs.L05PucciHarnackGridSelection
import Yau.LeafProofs.L05PucciHarnackBoxDecay
import Yau.LeafProofs.L05PucciHarnackDyadicNodeGeometry

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem harnack_grid_side_le {h0 : ℝ} (hh0 : 0 ≤ h0) (k : ℕ) : harnackGridSide h0 k ≤ h0 :=
  div_le_self hh0 (one_le_pow₀ (by norm_num))

theorem harnack_grid_decay_step {n m : ℕ} (hn : 0 < n) (hm : 0 < m) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) {u : Point n → ℝ} (hu : harnackSuper0 ell L u)
    {h0 : ℝ} (hh0 : 0 < h0) (hh01 : h0 ≤ 1/128)
    (hSpace : (Real.sqrt (2*n)+harnackLocalRadius n+3)*h0 ≤ 1/32)
    (hTime : (4*(m : ℝ)+6)*h0^2 ≤ 1/64)
    {z : Point n} (hz : z∈harnackQplus n) (hzLow : u z ≤ 1) (k : ℕ) :
    (volume : Measure (Point n)) (harnackDecayEvent n ell L m h0 u (k+1)) ≤
      ENNReal.ofReal ((1-harnackDelta n ell L)*(1+1/(m : ℝ)))*
        (volume : Measure (Point n)) (harnackDecayEvent n ell L m h0 u k) := by
  have hq0 : 0 ≤ 1-harnackDelta n ell L := by linarith [harnack_delta_le_quarter n ell L]
  have hq1 : 1-harnackDelta n ell L < 1 := by linarith [harnack_delta_pos (n := n) (L := L) hell]
  apply harnack_grid_selected_parent_transfer hh0 hq0 hq1 (by exact_mod_cast hm)
    (harnack_decayEvent_open hn hh0 hu.1 (k+1))
  · intro p hp Q hLevel hpQ
    have hpBox := hpQ
    rw [harnack_grid_node_box_eq] at hpBox
    have hSide : harnackGridSide h0 Q.1=h0 := by simp only [harnackGridSide,hLevel,pow_zero,div_one]
    rw [hSide] at hpBox
    have hND := harnack_buffer_root_not_dense hn hell hL hu hh0 hh01 hSpace hTime hz hzLow k hp.1 hpBox
    simpa only [harnackGridDense,harnack_grid_node_box_eq,hSide] using hND
  · intro P hP
    obtain ⟨Q,hQ,hQP⟩ := hP.1
    have hDense : (1-harnackDelta n ell L)*harnackMu (harnackGridNodeBox h0 Q) <
        harnackMu (harnackDecayEvent n ell L m h0 u (k+1) ∩ harnackGridNodeBox h0 Q) := hQ.2.1
    have hIntersectionPos : 0 < harnackMu
        (harnackDecayEvent n ell L m h0 u (k+1) ∩ harnackGridNodeBox h0 Q) :=
      lt_of_le_of_lt (mul_nonneg hq0 (by exact ENNReal.toReal_nonneg)) hDense
    have hNe : (volume : Measure (Point n))
        (harnackDecayEvent n ell L m h0 u (k+1) ∩ harnackGridNodeBox h0 Q) ≠ 0 := by
      intro hZero
      simp only [harnackMu,hZero,ENNReal.toReal_zero] at hIntersectionPos
      exact hIntersectionPos.false
    obtain ⟨p,hp,hpQ⟩ := nonempty_of_measure_ne_zero hNe
    have hpBox := hpQ
    rw [harnack_grid_node_box_eq] at hpBox
    rw [harnack_grid_node_box_eq] at hDense
    have hForward := harnack_dense_box_forward_parent hn hell hL hu hh0 hh01 hSpace hTime hz hzLow k
      (harnack_grid_side_pos hh0 Q.1) (harnack_grid_side_le hh0.le Q.1) hp.1 hpBox hDense
      (fun x hx => harnack_grid_node_parent_distance_to_child_center hh0 Q hQ.1 hx)
      (fun x hx => by simpa only [dist_comm] using harnack_grid_node_child_parent_distance hh0 Q hQ.1 hpQ.1 hx)
      (harnack_grid_node_parent_time_bounds hh0 Q hQ.1)
    rw [← hQP]
    have hSide := harnack_grid_node_parent_side h0 Q hQ.1
    have hLength : (m : ℝ)*(harnackGridSide h0 (harnackGridParent Q).1)^2=
        4*(m : ℝ)*(harnackGridSide h0 Q.1)^2 := by rw [hSide]; ring
    simpa only [hLength] using hForward


theorem harnack_distribution_decay {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) :
    ∃ H0 K q A : ℝ, 0 < H0 ∧ 1 < K ∧ 0 < q ∧ q < 1 ∧ 0 < A ∧
      ∀ u : Point n → ℝ, harnackSuper0 ell L u →
      (∃ z∈harnackQplus n, u z ≤ 1) → ∀ k : ℕ,
        harnackMu (harnackQminus n ∩ {p | H0*K^k < u p}) ≤ A*q^k := by
  let m := harnackIterationM n ell L
  have hm : 0 < m := harnack_iterationM_pos n ell L
  obtain ⟨J,hSmall⟩ := harnack_small_grid_scale_exists n m
  let h0 : ℝ := (1/2)^J
  have hh0 : 0 < h0 := pow_pos (by norm_num) _
  change h0 ≤ 1/128 ∧ (Real.sqrt (2*n)+harnackLocalRadius n+3)*h0 ≤ 1/32 ∧
    (4*(m : ℝ)+6)*h0^2 ≤ 1/64 at hSmall
  let H0 := harnackDecayInitialLevel n ell L m h0
  let K := harnackDecayRatio n ell L m
  let q := harnackIterationQ n ell L
  let A := harnackMu (harnackBufferDomain n m h0 0)
  have hH0 : 0 < H0 := harnack_decayInitialLevel_pos hn ell L hh0
  have hK : 1 < K := lt_of_lt_of_le (by norm_num) (harnack_decayRatio_bounds n ell L m).1
  have hq : 0 < q ∧ q < 1 := ⟨(harnack_iterationQ_bounds (n := n) (L := L) hell).1,
    (harnack_iterationQ_bounds (n := n) (L := L) hell).2.2⟩
  have hA : 0 < A := harnack_buffer_mu_pos hn hh0 0
  refine ⟨H0,K,q,A,hH0,hK,hq.1,hq.2,hA,?_⟩
  intro u hu hz
  obtain ⟨z,hz,hzLow⟩ := hz
  have hStep (k : ℕ) : harnackMu (harnackDecayEvent n ell L m h0 u (k+1)) ≤
      q*harnackMu (harnackDecayEvent n ell L m h0 u k) := by
    have hENN := harnack_grid_decay_step hn hm hell hL hu hh0 hSmall.1 hSmall.2.1 hSmall.2.2 hz hzLow k
    have hFin : ENNReal.ofReal q*(volume : Measure (Point n))
        (harnackDecayEvent n ell L m h0 u k) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (harnack_decayEvent_measure_ne_top hn hh0 u k)
    have hReal := ENNReal.toReal_mono hFin hENN
    simpa only [harnackMu,ENNReal.toReal_mul,ENNReal.toReal_ofReal hq.1.le] using hReal
  have hBound (k : ℕ) : harnackMu (harnackDecayEvent n ell L m h0 u k) ≤ A*q^k := by
    induction k with
    | zero =>
      rw [pow_zero,mul_one]
      exact harnack_mu_mono (harnack_buffer_measure_ne_top hn hh0 0)
        (show harnackDecayEvent n ell L m h0 u 0 ⊆ harnackBufferDomain n m h0 0 from inter_subset_left)
    | succ k ih =>
      calc
        _ ≤ q*harnackMu (harnackDecayEvent n ell L m h0 u k) := hStep k
        _ ≤ q*(A*q^k) := mul_le_mul_of_nonneg_left ih hq.1.le
        _ = A*q^(k+1) := by rw [pow_succ]; ring
  intro k
  have hSub : (harnackQminus n ∩ {p | H0*K^k < u p}) ⊆ harnackDecayEvent n ell L m h0 u k := by
    intro p hp
    exact ⟨harnack_qminus_subset_buffer hn hh0 k hp.1,hp.2⟩
  exact (harnack_mu_mono (harnack_decayEvent_measure_ne_top hn hh0 u k) hSub).trans (hBound k)

end Yau.LeafProofs.L05Aux

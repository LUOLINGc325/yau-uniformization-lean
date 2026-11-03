import Yau.LeafProofs.L05PucciHarnackDecayConstants

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def harnackDecayEvent (n : ℕ) (ell L : ℝ) (m : ℕ) (h0 : ℝ) (u : Point n → ℝ) (k : ℕ) : Set (Point n) :=
  harnackBufferDomain n m h0 k ∩
    {z | harnackDecayInitialLevel n ell L m h0*(harnackDecayRatio n ell L m)^k < u z}

theorem harnack_decayEvent_open {n m : ℕ} (hn : 0 < n) {ell L h0 : ℝ} (hh0 : 0 < h0)
    {u : Point n → ℝ} (hu : ContinuousOn u (unitClosed n)) (k : ℕ) :
    IsOpen (harnackDecayEvent n ell L m h0 u k) := harnack_buffer_level_open hn hh0 k hu _

theorem harnack_decayEvent_measure_ne_top {n m : ℕ} (hn : 0 < n) {ell L h0 : ℝ}
    (hh0 : 0 < h0) (u : Point n → ℝ) (k : ℕ) :
    (volume : Measure (Point n)) (harnackDecayEvent n ell L m h0 u k) ≠ ⊤ :=
  ne_top_of_le_ne_top (harnack_buffer_measure_ne_top hn hh0 k) (measure_mono inter_subset_left)

theorem harnack_buffer_dense_box_small {n m : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) {u : Point n → ℝ} (hu : harnackSuper0 ell L u)
    {h0 : ℝ} (hh0 : 0 < h0) (hh01 : h0 ≤ 1/128)
    (hSpace : (Real.sqrt (2*n)+harnackLocalRadius n+3)*h0 ≤ 1/32)
    (hTime : (4*(m : ℝ)+6)*h0^2 ≤ 1/64)
    {z : Point n} (hz : z∈harnackQplus n) (hzLow : u z ≤ 1)
    (k : ℕ) {c : Space n} {r a : ℝ} (hr : 0 < r) (hr0 : r ≤ h0)
    {p : Point n} (hp : p∈harnackBufferDomain n m h0 (k+1)) (hpBox : p∈harnackBox c r a)
    (hDense : (1-harnackDelta n ell L)*harnackMu (harnackBox c r a) <
      harnackMu (harnackDecayEvent n ell L m h0 u (k+1) ∩ harnackBox c r a)) :
    r < harnackBufferRho n m h0*(1/4 : ℝ)^k := by
  have hp0 := harnack_buffer_domain_antitone (m := m) hn hh0 (Nat.zero_le (k+1)) hp
  have hDist : dist c p.1 ≤ Real.sqrt (2*n)*r/2 := by
    have h := harnack_cube_subset_closedBall c hr.le hpBox.1
    simpa only [Metric.mem_closedBall,dist_comm] using h
  have hBudgets := harnack_cube_cylinder_budgets hn hh0 hSpace hTime hr hr0 hp0 hDist hpBox.2
  have hH0 := harnack_decayInitialLevel_pos (m := m) hn ell L hh0
  have hKpos : 0 < harnackDecayRatio n ell L m :=
    lt_of_lt_of_le (by norm_num) (harnack_decayRatio_bounds n ell L m).1
  have hLevel : 0 < harnackDecayInitialLevel n ell L m h0*(harnackDecayRatio n ell L m)^(k+1) :=
    mul_pos hH0 (pow_pos hKpos _)
  let H := harnackDecayInitialLevel n ell L m h0*(harnackDecayRatio n ell L m)^(k+1)
  have hTargetFin : (volume : Measure (Point n)) (harnackBox c r a ∩ {x | H < u x}) ≠ ⊤ :=
    ne_top_of_le_ne_top (harnack_box_measure_ne_top c hr a) (measure_mono inter_subset_left)
  have hDensityFull : (1-harnackDelta n ell L)*harnackMu (harnackBox c r a) <
      harnackMu (harnackBox c r a ∩ {x | H < u x}) := hDense.trans_le
    (harnack_mu_mono hTargetFin (fun x hx => ⟨hx.2,hx.1.2⟩))
  have hRadius := harnack_dense_cube_radius_bound hn hell hL hu hBudgets.1 hr (hr0.trans hh01)
    hBudgets.2.1 hLevel (fun x hx => unitOpen_subset_unitClosed (hBudgets.2.2.1 hx))
    (fun x hx => hBudgets.2.2.1 (harnack_open_subset_closed hx)) hDensityFull hz hzLow
  exact harnack_decay_level_radius hn hell hh0 hr.le k hRadius

theorem harnack_buffer_root_not_dense {n m : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) {u : Point n → ℝ} (hu : harnackSuper0 ell L u)
    {h0 : ℝ} (hh0 : 0 < h0) (hh01 : h0 ≤ 1/128)
    (hSpace : (Real.sqrt (2*n)+harnackLocalRadius n+3)*h0 ≤ 1/32)
    (hTime : (4*(m : ℝ)+6)*h0^2 ≤ 1/64)
    {z : Point n} (hz : z∈harnackQplus n) (hzLow : u z ≤ 1)
    (k : ℕ) {c : Space n} {a : ℝ} {p : Point n}
    (hp : p∈harnackBufferDomain n m h0 (k+1)) (hpBox : p∈harnackBox c h0 a) :
    ¬((1-harnackDelta n ell L)*harnackMu (harnackBox c h0 a) <
      harnackMu (harnackDecayEvent n ell L m h0 u (k+1) ∩ harnackBox c h0 a)) := by
  intro hDense
  have hSmall := harnack_buffer_dense_box_small hn hell hL hu hh0 hh01 hSpace hTime
    hz hzLow k hh0 le_rfl hp hpBox hDense
  have hPow : (1/4 : ℝ)^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hRho := harnack_bufferRho_pos (m := m) hn hh0
  have hScale := mul_le_mul_of_nonneg_left hPow hRho.le
  have hBound := (harnack_bufferRho_bounds n m h0).1
  rw [mul_one] at hScale
  linarith


theorem harnack_dense_box_forward_parent {n m : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) {u : Point n → ℝ} (hu : harnackSuper0 ell L u)
    {h0 : ℝ} (hh0 : 0 < h0) (hh01 : h0 ≤ 1/128)
    (hSpace : (Real.sqrt (2*n)+harnackLocalRadius n+3)*h0 ≤ 1/32)
    (hTime : (4*(m : ℝ)+6)*h0^2 ≤ 1/64)
    {z : Point n} (hz : z∈harnackQplus n) (hzLow : u z ≤ 1)
    (k : ℕ) {c : Space n} {r a : ℝ} (hr : 0 < r) (hr0 : r ≤ h0)
    {p : Point n} (hp : p∈harnackBufferDomain n m h0 (k+1)) (hpBox : p∈harnackBox c r a)
    (hDense : (1-harnackDelta n ell L)*harnackMu (harnackBox c r a) <
      harnackMu (harnackDecayEvent n ell L m h0 u (k+1) ∩ harnackBox c r a))
    {S : Set (Space n)} {bP : ℝ}
    (hSCenter : ∀ x∈S, dist x c ≤ (3/2)*Real.sqrt (2*n)*r)
    (hSPoint : ∀ x∈S, dist x p.1 ≤ 2*Real.sqrt (2*n)*r)
    (hTop : a+r^2 ≤ bP ∧ bP ≤ a+4*r^2) :
    S ×ˢ Ioc bP (bP+4*(m : ℝ)*r^2) ⊆ harnackDecayEvent n ell L m h0 u k := by
  have hp0 := harnack_buffer_domain_antitone (m := m) hn hh0 (Nat.zero_le (k+1)) hp
  have hDist : dist c p.1 ≤ Real.sqrt (2*n)*r/2 := by
    simpa only [Metric.mem_closedBall,dist_comm] using
      harnack_cube_subset_closedBall c hr.le hpBox.1
  have hBudgets := harnack_cube_cylinder_budgets hn hh0 hSpace hTime hr hr0 hp0 hDist hpBox.2
  have hH0 := harnack_decayInitialLevel_pos (m := m) hn ell L hh0
  have hKpos : 0 < harnackDecayRatio n ell L m :=
    lt_of_lt_of_le (by norm_num) (harnack_decayRatio_bounds n ell L m).1
  let H := harnackDecayInitialLevel n ell L m h0*(harnackDecayRatio n ell L m)^(k+1)
  have hH : 0 < H := mul_pos hH0 (pow_pos hKpos _)
  have hM : 0 < harnackLocalM n ell L := lt_trans (by norm_num) (harnack_localM_gt_one n ell L)
  have hNormH : 0 < H/harnackLocalM n ell L := div_pos hH hM
  have hTargetFin : (volume : Measure (Point n)) (harnackBox c r a ∩ {x | H < u x}) ≠ ⊤ :=
    ne_top_of_le_ne_top (harnack_box_measure_ne_top c hr a) (measure_mono inter_subset_left)
  have hDensityFull : (1-harnackDelta n ell L)*harnackMu (harnackBox c r a) <
      harnackMu (harnackBox c r a ∩ {x | harnackLocalM n ell L*(H/harnackLocalM n ell L) < u x}) := by
    rw [mul_div_cancel₀ H hM.ne']
    exact hDense.trans_le (harnack_mu_mono hTargetFin (fun x hx => ⟨hx.2,hx.1.2⟩))
  have hSeed := harnack_cube_density_forward hell hL hu hr hNormH
    (fun x hx => unitOpen_subset_unitClosed (hBudgets.2.2.1 hx))
    (fun x hx => hBudgets.2.2.1 (harnack_open_subset_closed hx)) hDensityFull
  have hStack := harnack_positive_ball_stack hn hell hL hu hr hNormH m
    (fun x hx => unitOpen_subset_unitClosed (hBudgets.2.2.2 hx))
    (fun x hx => hBudgets.2.2.2 (harnack_open_subset_closed hx))
    (fun x hx => (hSeed (x,a+r^2) ⟨hx,le_rfl,by nlinarith [sq_nonneg r]⟩).le)
  have hSmall := harnack_buffer_dense_box_small hn hell hL hu hh0 hh01 hSpace hTime hz hzLow k hr hr0 hp hpBox hDense
  have hLevel := harnack_decay_stack_level (n := n) (m := m) (ell := ell) (L := L) hH0 k
  have hCurrent : 0 < harnackDecayInitialLevel n ell L m h0*(harnackDecayRatio n ell L m)^k :=
    mul_pos hH0 (pow_pos hKpos _)
  intro y hy
  have hTimeLo : p.2 ≤ y.2 := by linarith [hpBox.2.2,hy.2.1]
  have hTimeHi : y.2 ≤ p.2+4*((m : ℝ)+1)*r^2 := by
    nlinarith [hpBox.2.1,hy.2.2]
  refine ⟨harnack_forward_stack_in_buffer hn hh0 k hr hSmall hp (hSPoint _ hy.1) hTimeLo hTimeHi,?_⟩
  have hStackPoint := hStack y ⟨hSCenter _ hy.1,by linarith [hy.2.1],?_⟩
  · change _ < u y
    change harnackStackBeta n ell L m*(H/harnackLocalM n ell L) ≤ u y at hStackPoint
    change 2*(harnackDecayInitialLevel n ell L m h0*(harnackDecayRatio n ell L m)^k) ≤
      harnackStackBeta n ell L m*(H/harnackLocalM n ell L) at hLevel
    linarith
  · unfold harnackStackDuration
    nlinarith [hy.2.2]

end Yau.LeafProofs.L05Aux

import Yau.LeafProofs.L05ParabolicClassical
import Yau.LeafProofs.L05PerronPolynomials

noncomputable section

open Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

def chuAnchorDomain (n : ℕ) : Set (Point n) :=
  Metric.closedBall 0 (1/2) ×ˢ Set.Icc (-(3/4:ℝ)) (-(1/4))

def chuAnchorOpen (n : ℕ) : Set (Point n) :=
  Metric.ball 0 (1/2) ×ˢ Set.Ioo (-(3/4:ℝ)) (-(1/4))

def chuAnchorCenter (n : ℕ) : Point n := (0,-(1/2:ℝ))

def chuAnchorScale (B : ℝ) : ℝ := 64*(1+B)

def chuAnchorPenalty {n : ℕ} (a : ℝ) : Point n → ℝ :=
  perronSeparatedPolynomial 0 (chuAnchorCenter n) 0 0 a a

theorem chuAnchorPenalty_apply {n : ℕ} (a : ℝ) (p : Point n) :
    chuAnchorPenalty a p=a*(‖p.1‖^2+(p.2+(1/2:ℝ))^2) := by
  rw [chuAnchorPenalty,perronSeparatedPolynomial_apply]
  simp only [chuAnchorCenter,sub_zero,inner_zero_left,zero_add,zero_mul,add_zero,sub_neg_eq_add]
  ring

theorem chuAnchorPenalty_smooth {n : ℕ} (a : ℝ) : ContDiff ℝ ∞ (@chuAnchorPenalty n a) :=
  perronSeparatedPolynomial_smooth _ _ _ _ _ _

theorem chuAnchorPenalty_center {n : ℕ} (a : ℝ) : chuAnchorPenalty a (chuAnchorCenter n)=0 := by
  rw [chuAnchorPenalty,perronSeparatedPolynomial_center]

theorem chuAnchorDomain_compact (n : ℕ) : IsCompact (chuAnchorDomain n) :=
  (isCompact_closedBall (0 : Space n) (1/2)).prod isCompact_Icc

theorem chuAnchorCenter_mem (n : ℕ) : chuAnchorCenter n ∈ chuAnchorDomain n := by
  refine ⟨Metric.mem_closedBall_self (by norm_num),?_⟩
  norm_num [chuAnchorCenter]

theorem chuAnchorDomain_subset_backward {n : ℕ} : chuAnchorDomain n ⊆ backward 1 := by
  intro p hp
  refine ⟨Metric.closedBall_subset_ball (by norm_num : (1/2:ℝ) < 1) hp.1,?_,?_⟩ <;>
    linarith only [hp.2.1,hp.2.2]

theorem chuAnchorOpen_subset_domain {n : ℕ} : chuAnchorOpen n ⊆ chuAnchorDomain n :=
  fun _ hp => ⟨Metric.ball_subset_closedBall hp.1,hp.2.1.le,hp.2.2.le⟩

theorem chuAnchorOpen_isOpen (n : ℕ) : IsOpen (chuAnchorOpen n) :=
  Metric.isOpen_ball.prod isOpen_Ioo

set_option maxHeartbeats 1400000 in
theorem chuAnchor_minimum {n : ℕ} {B : ℝ} (hB : 0 ≤ B) {u : Point n → ℝ}
    (hu : ContinuousOn u (chuAnchorDomain n)) (hb : ∀ p ∈ chuAnchorDomain n, |u p| ≤ B) :
    ∃ p ∈ chuAnchorOpen n, IsLocalMin (fun q => u q+chuAnchorPenalty (chuAnchorScale B) q) p := by
  let a := chuAnchorScale B
  have ha : 0 < a := by dsimp only [a,chuAnchorScale]; positivity
  have hc := hu.add (chuAnchorPenalty_smooth a).continuous.continuousOn
  obtain ⟨p,hp,hm⟩ := (chuAnchorDomain_compact n).exists_isMinOn ⟨chuAnchorCenter n,chuAnchorCenter_mem n⟩ hc
  have hcval : u p+chuAnchorPenalty a p ≤ u (chuAnchorCenter n)+chuAnchorPenalty a (chuAnchorCenter n) :=
    hm (chuAnchorCenter_mem n)
  rw [chuAnchorPenalty_center,add_zero] at hcval
  have hcenter := (abs_le.mp (hb _ (chuAnchorCenter_mem n))).2
  have hplow := (abs_le.mp (hb p hp)).1
  have hpen : a*(‖p.1‖^2+(p.2+(1/2:ℝ))^2) ≤ 2*B := by
    rw [← chuAnchorPenalty_apply]
    linarith only [hcval,hcenter,hplow]
  have hspace : ‖p.1‖ < (1/2:ℝ) := by
    have hle : ‖p.1‖ ≤ (1/2:ℝ) := by simpa only [Metric.mem_closedBall,dist_zero_right] using hp.1
    by_contra hn
    have he := le_antisymm hle (le_of_not_gt hn)
    rw [he] at hpen
    have hnon := mul_nonneg ha.le (sq_nonneg (p.2+(1/2:ℝ)))
    dsimp only [a,chuAnchorScale] at hpen hnon
    nlinarith only [hpen,hnon,hB]
  have hlow : -(3/4:ℝ) < p.2 := by
    by_contra hn
    have he := le_antisymm (le_of_not_gt hn) hp.2.1
    rw [he] at hpen
    have hnon := mul_nonneg ha.le (sq_nonneg ‖p.1‖)
    dsimp only [a,chuAnchorScale] at hpen hnon
    nlinarith only [hpen,hnon,hB]
  have hupp : p.2 < -(1/4:ℝ) := by
    by_contra hn
    have he := le_antisymm hp.2.2 (le_of_not_gt hn)
    rw [he] at hpen
    have hnon := mul_nonneg ha.le (sq_nonneg ‖p.1‖)
    dsimp only [a,chuAnchorScale] at hpen hnon
    nlinarith only [hpen,hnon,hB]
  have hpO : p ∈ chuAnchorOpen n := ⟨by simpa only [Metric.mem_ball,dist_zero_right] using hspace,hlow,hupp⟩
  refine ⟨p,hpO,?_⟩
  have hnear : chuAnchorDomain n ∈ 𝓝 p := mem_of_superset ((chuAnchorOpen_isOpen n).mem_nhds hpO)
    chuAnchorOpen_subset_domain
  filter_upwards [hnear] with q hq
  exact hm hq

def chuAnchorLowerTest {n : ℕ} (a : ℝ) (u : Point n → ℝ) (p : Point n) : Point n → ℝ :=
  perronSeparatedPolynomial (u p+chuAnchorPenalty a p) (chuAnchorCenter n) 0 0 (-a) (-a)

def chuAnchorUpperTest {n : ℕ} (a : ℝ) (u : Point n → ℝ) (p : Point n) : Point n → ℝ :=
  perronSeparatedPolynomial (u p-chuAnchorPenalty a p) (chuAnchorCenter n) 0 0 a a

theorem chuAnchorLowerTest_apply {n : ℕ} (a : ℝ) (u : Point n → ℝ) (p q : Point n) :
    chuAnchorLowerTest a u p q=u p+chuAnchorPenalty a p-chuAnchorPenalty a q := by
  rw [chuAnchorLowerTest,perronSeparatedPolynomial_apply]
  simp only [chuAnchorPenalty_apply,chuAnchorCenter,sub_zero,inner_zero_left,zero_add,zero_mul,add_zero,sub_neg_eq_add]
  ring

theorem chuAnchorUpperTest_apply {n : ℕ} (a : ℝ) (u : Point n → ℝ) (p q : Point n) :
    chuAnchorUpperTest a u p q=u p-chuAnchorPenalty a p+chuAnchorPenalty a q := by
  rw [chuAnchorUpperTest,perronSeparatedPolynomial_apply]
  simp only [chuAnchorPenalty_apply,chuAnchorCenter,sub_zero,inner_zero_left,zero_add,zero_mul,add_zero,sub_neg_eq_add]
  ring

theorem chuAnchorLowerTest_touch {n : ℕ} {a : ℝ} {u : Point n → ℝ} {p : Point n}
    (hm : IsLocalMin (fun q => u q+chuAnchorPenalty a q) p) : touchBelow (chuAnchorLowerTest a u p) u p := by
  refine ⟨by rw [chuAnchorLowerTest_apply]; ring,?_⟩
  filter_upwards [hm] with q hq
  rw [chuAnchorLowerTest_apply]
  linarith only [hq]

theorem chuAnchorUpperTest_touch {n : ℕ} {a : ℝ} {u : Point n → ℝ} {p : Point n}
    (hm : IsLocalMin (fun q => -u q+chuAnchorPenalty a q) p) : touchAbove (chuAnchorUpperTest a u p) u p := by
  refine ⟨by rw [chuAnchorUpperTest_apply]; ring,?_⟩
  filter_upwards [hm] with q hq
  rw [chuAnchorUpperTest_apply]
  linarith only [hq]

theorem chuAnchorLowerTest_smooth {n : ℕ} (a : ℝ) (u : Point n → ℝ) (p : Point n) :
    ContDiff ℝ ∞ (chuAnchorLowerTest a u p) := perronSeparatedPolynomial_smooth _ _ _ _ _ _

theorem chuAnchorUpperTest_smooth {n : ℕ} (a : ℝ) (u : Point n → ℝ) (p : Point n) :
    ContDiff ℝ ∞ (chuAnchorUpperTest a u p) := perronSeparatedPolynomial_smooth _ _ _ _ _ _

theorem chuAnchorLowerTest_timeD {n : ℕ} (a : ℝ) (u : Point n → ℝ) (p : Point n) :
    timeD Set.univ (chuAnchorLowerTest a u p) p= -2*a*(p.2+(1/2:ℝ)) := by
  rw [chuAnchorLowerTest,perronSeparatedPolynomial_timeD]
  simp only [chuAnchorCenter,zero_add,sub_neg_eq_add]
  ring

theorem chuAnchorUpperTest_timeD {n : ℕ} (a : ℝ) (u : Point n → ℝ) (p : Point n) :
    timeD Set.univ (chuAnchorUpperTest a u p) p=2*a*(p.2+(1/2:ℝ)) := by
  rw [chuAnchorUpperTest,perronSeparatedPolynomial_timeD]
  simp only [chuAnchorCenter,zero_add,sub_neg_eq_add]

theorem chuAnchorLowerTest_hessian {n : ℕ} (a : ℝ) (u : Point n → ℝ) (p : Point n) :
    (hessian (chuAnchorLowerTest a u p) p : Mat n)= -((2*a) • (1 : Mat n)) := by
  rw [chuAnchorLowerTest,perronSeparatedPolynomial_hessian_coe,← neg_smul]
  congr 1
  ring

theorem chuAnchorUpperTest_hessian {n : ℕ} (a : ℝ) (u : Point n → ℝ) (p : Point n) :
    (hessian (chuAnchorUpperTest a u p) p : Mat n)=(2*a) • (1 : Mat n) :=
  perronSeparatedPolynomial_hessian_coe _ _ _ _ _ _ _

theorem chuAnchorOpen_subset_unitOpen {n : ℕ} : chuAnchorOpen n ⊆ unitOpen n := by
  intro p hp
  refine ⟨Metric.ball_subset_ball (by norm_num : (1/2:ℝ) ≤ 1) hp.1,?_,?_⟩ <;>
    linarith only [hp.2.1,hp.2.2]

theorem chu_unitOpen_subset_backward {n : ℕ} : unitOpen n ⊆ backward 1 :=
  fun _ hp => ⟨hp.1,by simpa only [one_pow] using hp.2.1,hp.2.2.le⟩

end Yau.LeafProofs.L05Aux

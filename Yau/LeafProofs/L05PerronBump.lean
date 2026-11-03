import Yau.LeafProofs.L05PerronBarrierBounds
import Yau.LeafProofs.L05PerronQuartic

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

def perronScaledQuadratic {n : ℕ} (a : ℝ) (p q : Point n) : ℝ := a*qnorm2 (q-p)

theorem perronScaledQuadratic_eq {n : ℕ} (a : ℝ) (p : Point n) :
    perronScaledQuadratic a p=perronSeparatedPolynomial 0 p 0 0 a a := by
  funext q
  rw [perronSeparatedPolynomial_apply]
  simp only [perronScaledQuadratic,qnorm2,Prod.fst_sub,Prod.snd_sub,
    inner_zero_left,zero_add,zero_mul,add_zero]
  ring

theorem perronScaledQuadratic_smooth {n : ℕ} (a : ℝ) (p : Point n) :
    ContDiff ℝ ∞ (perronScaledQuadratic a p) := by
  rw [perronScaledQuadratic_eq]
  exact perronSeparatedPolynomial_smooth _ _ _ _ _ _

theorem perronScaledQuadratic_timeD {n : ℕ} (a : ℝ) (p : Point n) :
    timeD Set.univ (perronScaledQuadratic a p) p=0 := by
  rw [perronScaledQuadratic_eq,perronSeparatedPolynomial_timeD]
  simp

theorem perronScaledQuadratic_hessian {n : ℕ} (a : ℝ) (p : Point n) :
    hessian (perronScaledQuadratic a p) p=(2*a) • sym (1 : Mat n) := by
  rw [perronScaledQuadratic_eq,perronSeparatedPolynomial_hessian]

set_option maxHeartbeats 1800000 in
theorem perron_failed_lower_test_bump {n : ℕ} (hn : 0 < n)
    {ell L : ℝ} (hell : 0 < ell) (hL : ell ≤ L)
    {F : Sym n → ℝ} (hF : Continuous F) (hE : globalElliptic F ell L)
    (h0 : F 0=0) {B : ℝ} {v : Point n → ℝ}
    {Q : Set (Point n)} (hQ : IsOpen Q) {p : Point n} (hp : p ∈ Q)
    (hb : ∀ q ∈ Q, v q ≤ B) {phi : Point n → ℝ}
    (hc : ContDiffAt ℝ 2 phi p) (ht : touchBelow phi v p)
    (hfail : timeD Set.univ phi p-F (hessian phi p) < 0) :
    ∃ r delta : ℝ, 0 < r ∧ 0 < delta ∧ Metric.closedBall p r ⊆ Q ∧
      ∃ z : Point n → ℝ,
        ContinuousOn z (Metric.closedBall p r) ∧ z p=v p+delta ∧
        viscositySub (Metric.ball p r) (fun H _ => F H) (fun _ => 0) z ∧
        (∀ q ∈ Metric.closedBall p r, z q < B) ∧
        (∀ q, r/2 ≤ dist q p → dist q p ≤ r → z q ≤ v q) := by
  have hvB : v p < B := by
    by_contra hnot
    have he : v p=B := le_antisymm (hb p hp) (le_of_not_gt hnot)
    have hm : IsLocalMax phi p := by
      filter_upwards [ht.2,hQ.mem_nhds hp] with q hq hqQ
      change phi q ≤ phi p
      rw [ht.1,he]
      exact hq.trans (hb q hqQ)
    have htime := perron_localMax_timeD_zero hc hm
    have hH := perron_localMax_hessian_nonpos hc hm
    have hmono : F (hessian phi p) ≤ F 0 :=
      perron_globalElliptic_mono hell.le hE (by rw [zero_sub]; convert! hH using 1)
    rw [h0] at hmono
    rw [htime] at hfail
    linarith
  have hd : 0 < (Fintype.card (Yau.RIdx n):ℝ) := by
    simp only [Yau.RIdx,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
    positivity
  have hLp : 0 < L := hell.trans_le hL
  let a0 := -(timeD Set.univ phi p-F (hessian phi p))/(4*(Fintype.card (Yau.RIdx n):ℝ)*L)
  have ha0 : 0 < a0 := by
    exact div_pos (neg_pos.mpr hfail) (by positivity)
  let psi := fun q : Point n => phi q-perronScaledQuadratic a0 p q
  have hquad : ContDiffAt ℝ 2 (perronScaledQuadratic a0 p) p :=
    (perronScaledQuadratic_smooth a0 p).contDiffAt.of_le (by simp)
  have hpsi : ContDiffAt ℝ 2 psi p := hc.sub hquad
  have htime : timeD Set.univ psi p=timeD Set.univ phi p := by
    change timeD Set.univ (fun q => phi q-perronScaledQuadratic a0 p q) p=_
    rw [perron_timeD_sub hc hquad,perronScaledQuadratic_timeD,sub_zero]
  have hH : hessian psi p=hessian phi p-(2*a0) • sym (1 : Mat n) := by
    change hessian (fun q => phi q-perronScaledQuadratic a0 p q) p=_
    rw [perron_hessian_sub hc hquad,perronScaledQuadratic_hessian]
  have hi : (sym (1 : Mat n) : Mat n)=1 :=
    IsSelfAdjoint.coe_selfAdjointPart_apply ℝ (IsSelfAdjoint.one _)
  have hP : (((2*a0) • sym (1 : Mat n) : Sym n) : Mat n).PosSemidef := by
    change ((2*a0) • (sym (1 : Mat n) : Mat n)).PosSemidef
    rw [hi]
    exact Matrix.PosSemidef.one.smul (by positivity)
  have htr : Matrix.trace (((2*a0) • sym (1 : Mat n) : Sym n) : Mat n)=
      (2*a0)*(Fintype.card (Yau.RIdx n):ℝ) := by
    change Matrix.trace ((2*a0) • (sym (1 : Mat n) : Mat n))=_
    rw [hi,Matrix.trace_smul,smul_eq_mul,Matrix.trace_one]
  have hEll := (hE (hessian phi p-(2*a0) • sym (1 : Mat n)) ((2*a0) • sym (1 : Mat n)) hP).2
  rw [sub_add_cancel,htr] at hEll
  have haeq : a0*(4*(Fintype.card (Yau.RIdx n):ℝ)*L)= -(timeD Set.univ phi p-F (hessian phi p)) := by
    dsimp only [a0]
    field_simp
  have hres : timeD Set.univ psi p-F (hessian psi p) < 0 := by
    rw [htime,hH]
    nlinarith only [hEll,haeq,hfail]
  obtain ⟨V,hVo,hpV,hV2,hTc,hHc⟩ := perron_local_c2_jets hpsi
  have hRcont : ContinuousOn (fun q => timeD Set.univ psi q-F (hessian psi q)) V := by
    intro q hq
    exact (hTc q hq).sub (hF.continuousAt.comp_continuousWithinAt (hHc q hq))
  have hRnear : ∀ᶠ q in 𝓝 p, timeD Set.univ psi q-F (hessian psi q) < 0 :=
    ((hRcont p hpV).continuousAt (hVo.mem_nhds hpV)).tendsto (eventually_lt_nhds hres)
  let gamma := B-v p
  have hgamma : 0 < gamma := sub_pos.mpr hvB
  have hPhiNear : ∀ᶠ q in 𝓝 p, phi q < v p+gamma/4 :=
    hc.continuousAt.tendsto (eventually_lt_nhds (by rw [ht.1]; linarith))
  have hgood : ∀ᶠ q in 𝓝 p,
      q ∈ Q ∧ q ∈ V ∧ phi q ≤ v q ∧ phi q < v p+gamma/4 ∧
        timeD Set.univ psi q-F (hessian psi q) < 0 := by
    filter_upwards [hQ.mem_nhds hp,hVo.mem_nhds hpV,ht.2,hPhiNear,hRnear] with q hqQ hqV hqt hqPhi hqR
    exact ⟨hqQ,hqV,hqt,hqPhi,hqR⟩
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp hgood
  let r := R/2
  have hr : 0 < r := by dsimp only [r]; positivity
  have hKgood (q : Point n) (hq : q ∈ Metric.closedBall p r) :
      q ∈ Q ∧ q ∈ V ∧ phi q ≤ v q ∧ phi q < v p+gamma/4 ∧
        timeD Set.univ psi q-F (hessian psi q) < 0 :=
    hball (Metric.closedBall_subset_ball (show r < R by dsimp only [r]; linarith) hq)
  obtain ⟨delta,hdelta,hdsmall⟩ := exists_between (show 0 < min (a0*r^2/8) (gamma/4) by positivity)
  have hd1 : delta < a0*r^2/8 := hdsmall.trans_le (min_le_left _ _)
  have hd2 : delta < gamma/4 := hdsmall.trans_le (min_le_right _ _)
  let z := fun q : Point n => psi q+delta
  have hzC : ContinuousOn z (Metric.closedBall p r) := by
    intro q hq
    exact ((hV2 q (hKgood q hq).2.1).continuousAt.add continuousAt_const).continuousWithinAt
  have hzSub : viscositySub (Metric.ball p r) (fun H _ => F H) (fun _ => 0) z := by
    have hs : viscositySub (Metric.ball p r) (fun H _ => F H) (fun _ => 0) psi := by
      apply perron_classical_sub hell hE
      · intro q hq
        exact hV2 q (hKgood q (Metric.ball_subset_closedBall hq)).2.1
      · intro q hq
        exact (hKgood q (Metric.ball_subset_closedBall hq)).2.2.2.2.le
    exact viscositySub_add_const hs delta
  refine ⟨r,delta,hr,hdelta,(fun q hq => (hKgood q hq).1),z,hzC,?_,hzSub,?_,?_⟩
  · simp [z,psi,perronScaledQuadratic,qnorm2,ht.1]
  · intro q hq
    have hh := (hKgood q hq).2.2.2.1
    have hqn : 0 ≤ perronScaledQuadratic a0 p q := mul_nonneg ha0.le (qnorm2_nonneg _)
    dsimp only [z,psi,gamma] at *
    linarith
  · intro q hqlo hqhi
    have hqK : q ∈ Metric.closedBall p r := Metric.mem_closedBall.mpr hqhi
    have htouch := (hKgood q hqK).2.2.1
    have hqnorm : dist q p^2 ≤ qnorm2 (q-p) := by simpa only [dist_eq_norm] using norm_sq_le_qnorm2 (q-p)
    have hsquare : r^2/4 ≤ dist q p^2 := by nlinarith [show 0 ≤ dist q p from dist_nonneg]
    have hscaled := mul_le_mul_of_nonneg_left (hsquare.trans hqnorm) ha0.le
    dsimp only [z,psi,perronScaledQuadratic]
    linarith

end Yau.LeafProofs.L05Aux

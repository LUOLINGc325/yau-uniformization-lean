import Yau.LeafProofs.L05AutonomousTimeDerivativeConstruction

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- The actual all-h slope error gives both native Pucci inequalities by stability. -/
theorem auto_td_derivative_pucci {n : ℕ} {ell L delta r R C d : ℝ}
    (hell : 0<ell) (hL : ell≤L) (hd : 0<delta)
    (hr : 0<r) (hrR : r<R) (hR1 : R<1) (hdwidth : 0<d)
    {F : Sym n → ℝ} (hE : globalElliptic F ell L) {u V : Point n → ℝ}
    (hu : ContinuousOn u (unitClosed n))
    (hsol : viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u)
    (hError : ∀ z∈autoClosed (0 : Space n) R 0, ∀ h : ℝ, 0<h → h≤d/2 →
      |autoTime u h z-V z|≤C*h^(delta/4)) :
    autoPucci ell L (autoOpen (0 : Space n) r 0) V := by
  have hr1 : r<1 := hrR.trans hR1
  let h0 := min (d/2) ((1-r^2)/2)
  have hh0 : 0<h0 := by dsimp only [h0]; apply lt_min <;> nlinarith only [hdwidth,hr,hr1]
  have hh0d : h0≤d/2 := min_le_left _ _
  have hh01 : r^2+h0<1 := by
    have h := min_le_right (d/2) ((1-r^2)/2)
    change h0≤_ at h
    nlinarith only [h,hr,hr1]
  let h (k : ℕ) := autoDyadicStep h0 k
  have hPos (k : ℕ) : 0<h k := auto_dyadicStep_pos hh0 k
  have hLe (k : ℕ) : h k≤h0 := auto_dyadicStep_le hh0.le k
  have hBuf (k : ℕ) : r^2+h k<1 := by linarith only [hh01,hLe k]
  have hclass (k : ℕ) : autoPucci ell L (autoOpen (0 : Space n) r 0) (autoTime u (h k)) :=
    auto_time_pucci hell hL hr hr1 hE hu hsol (hPos k) (hBuf k)
  have hcont (k : ℕ) : ContinuousOn (autoTime u (h k)) (autoOpen (0 : Space n) r 0) := by
    have hclosed : ContinuousOn (autoTime u (h k)) (autoClosed (0 : Space n) r 0) :=
      ((hu.mono (auto_td_closed_unit hr hr1)).sub
        (hu.comp (continuous_fst.prodMk (continuous_snd.sub continuous_const)).continuousOn
          (auto_td_shift_closed hr hr1 (hPos k).le (hBuf k).le))).div_const (h k)
    exact hclosed.mono fun z hz => ⟨Metric.ball_subset_closedBall hz.1,hz.2.1.le,hz.2.2.le⟩
  have hlimit : TendstoUniformlyOn (fun k => autoTime u (h k)) V atTop (autoOpen (0 : Space n) r 0) := by
    apply auto_uniform_limit_of_geometric_error (B := C*h0^(delta/4))
      (Real.rpow_nonneg (by norm_num : (0 : ℝ)≤1/2) (delta/4))
      (Real.rpow_lt_one (by norm_num : (0 : ℝ)≤1/2) (by norm_num : (1/2 : ℝ)<1) (by linarith only [hd] : 0<delta/4))
    intro k z hz
    have hzR : z∈autoClosed (0 : Space n) R 0 :=
      autoClosed_subset 0 hr.le hrR.le 0 ⟨Metric.ball_subset_closedBall hz.1,hz.2.1.le,hz.2.2.le⟩
    have he := hError z hzR (h k) (hPos k) ((hLe k).trans hh0d)
    rw [auto_dyadicStep_rpow hh0.le] at he
    simpa only [mul_assoc] using he
  refine ⟨?_,?_⟩
  · exact auto_locally_uniform_sub (autoOpen_isOpen _ _ _) (pucciPlus_continuous hell.le hL)
      hcont (fun k => (hclass k).1) hlimit.tendstoLocallyUniformlyOn
  · exact auto_locally_uniform_super (autoOpen_isOpen _ _ _) ((pucciPlus_continuous hell.le hL).comp continuous_neg).neg
      hcont (fun k => (hclass k).2) hlimit.tendstoLocallyUniformlyOn

/-- Only genuine fibres of backward r are used to identify its native timeD. -/
theorem auto_td_timeD_eq {n : ℕ} {r R : ℝ} (hr : 0<r) (hrR : r<R)
    {u V : Point n → ℝ}
    (hWithin : ∀ x∈Metric.closedBall (0 : Space n) R, ∀ t∈Icc (-R^2) 0,
      HasDerivWithinAt (fun s => u (x,s)) (V (x,t)) (Icc (-R^2) 0) t) :
    ∀ z∈backward r, timeD (backward r) u z=V z := by
  intro z hz
  have hxR : z.1∈Metric.closedBall (0 : Space n) R :=
    (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hrR.le)) hz.1
  have hsquare : r^2<R^2 := by nlinarith only [hr,hrR]
  have hsub : Ioc (-r^2) 0⊆Icc (-R^2) 0 := by
    intro t ht
    exact ⟨by linarith only [ht.1,hsquare],ht.2⟩
  have htR : z.2∈Icc (-R^2) 0 := hsub hz.2
  have hfibre : {t : ℝ | (z.1,t)∈backward r}=Ioc (-r^2) 0 := by
    ext t
    simp only [backward,mem_ofPred_eq,mem_prod,hz.1,true_and]
  rw [timeD,hfibre]
  exact ((hWithin z.1 hxR z.2 htR).mono hsub).derivWithin (uniqueDiffOn_Ioc (-r^2) 0 z.2 hz.2)

/-- The actual continuous derivative is integrable on every closed time segment. -/
theorem auto_td_interval_integrable {n : ℕ} {R : ℝ} {V : Point n → ℝ}
    (hV : ContinuousOn V (autoClosed 0 R 0)) {x : Space n}
    (hx : x∈Metric.closedBall (0 : Space n) R) {a b : ℝ}
    (ha : a∈Icc (-R^2) 0) (hb : b∈Icc (-R^2) 0) :
    IntervalIntegrable (fun t => V (x,t)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply hV.comp (continuous_const.prodMk continuous_id).continuousOn
  intro t ht
  refine ⟨hx,?_⟩
  have ht' : min a b ≤ t ∧ t ≤ max a b := ht
  simpa only [zero_sub,id_eq] using
    (show t∈Icc (-R^2) 0 from ⟨(le_min ha.1 hb.1).trans ht'.1,ht'.2.trans (max_le ha.2 hb.2)⟩)

end Yau.LeafProofs.L05AutonomousAux

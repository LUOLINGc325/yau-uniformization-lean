import Yau.LeafProofs.L05AutonomousOneStepFields
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section
open Filter Set MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

theorem oneStep_open_subset_closed {n : ℕ} (c : Space n) (R T : ℝ) :
    autoOpen c R T⊆autoClosed c R T :=
  Set.prod_mono Metric.ball_subset_closedBall Ioo_subset_Icc_self

theorem oneStep_open_of_closed_subset {n : ℕ} {c d : Space n} {R r T t : ℝ}
    (hr : r≠0) (hsub : autoClosed c R T⊆autoClosed d r t) :
    autoOpen c R T⊆autoOpen d r t := by
  have hi : autoOpen c R T⊆interior (autoClosed d r t) :=
    (autoOpen_isOpen c R T).subset_interior_iff.mpr
      ((oneStep_open_subset_closed c R T).trans hsub)
  simpa only [autoClosed,autoOpen,interior_prod_eq,interior_closedBall d hr,interior_Icc] using hi

theorem oneStep_restrict_full {n : ℕ} {O U S : Set (Point n)}
    (hO : MeasurableSet O) (hU : MeasurableSet U) (hUO : U⊆O)
    (hFull : ∀ᵐ p ∂volume.restrict O, p∈S) :
    ∀ᵐ p ∂volume.restrict U, p∈S := by
  apply (ae_restrict_iff' hU).mpr
  have hh := (ae_restrict_iff' hO).mp hFull
  filter_upwards [hh] with p hp hpU
  exact hp (hUO hpU)

theorem oneStep_good_closure {n : ℕ} (c : Space n) {R T : ℝ} (hR : 0<R)
    {S : Set (Point n)} (hFull : ∀ᵐ p ∂volume.restrict (autoOpen c R T), p∈S) :
    autoClosed c R T⊆closure (S∩autoOpen c R T) := by
  have hAE := (ae_restrict_iff' (autoOpen_isOpen c R T).measurableSet).mp hFull
  have hd : Dense {p : Point n | p∈autoOpen c R T → p∈S} :=
    MeasureTheory.Measure.dense_of_ae (μ := volume) hAE
  have hInside : autoOpen c R T⊆closure (S∩autoOpen c R T) :=
    (hd.open_subset_closure_inter (autoOpen_isOpen c R T)).trans
      (closure_mono (by intro p hp; exact ⟨hp.2 hp.1,hp.1⟩))
  have hh := closure_minimal hInside isClosed_closure
  rw [autoOpen,closure_prod_eq,closure_ball c hR.ne',
    closure_Ioo (by nlinarith [sq_pos_of_pos hR] : T-R^2≠T)] at hh
  exact hh

theorem oneStep_good_nonempty {n : ℕ} (c : Space n) {R T : ℝ} (hR : 0<R)
    {S : Set (Point n)} (hFull : ∀ᵐ p ∂volume.restrict (autoOpen c R T), p∈S) :
    (S∩autoClosed c R T).Nonempty := by
  have hne : (closure (S∩autoOpen c R T)).Nonempty :=
    (autoClosed_nonempty c hR.le T).mono (oneStep_good_closure c hR hFull)
  exact hne.of_closure.mono (inter_subset_inter_right S (oneStep_open_subset_closed c R T))

theorem oneStep_continuous_upper {n : ℕ} (c : Space n) {R T M : ℝ} (hR : 0<R)
    {S : Set (Point n)} (hFull : ∀ᵐ p ∂volume.restrict (autoOpen c R T), p∈S)
    {v : Point n → ℝ} (hv : ContinuousOn v (autoClosed c R T))
    (hb : ∀ p∈S∩autoClosed c R T, v p≤M) :
    ∀ p∈autoClosed c R T, v p≤M := by
  have hInside : S∩autoOpen c R T⊆autoClosed c R T :=
    fun _ hp => oneStep_open_subset_closed c R T hp.2
  have hClosure : closure (S∩autoOpen c R T)⊆autoClosed c R T :=
    closure_minimal hInside (autoClosed_isCompact c R T).isClosed
  intro p hp
  exact le_on_closure (fun q hq => hb q ⟨hq.1,hInside hq⟩)
    (hv.mono hClosure) continuousOn_const (oneStep_good_closure c hR hFull hp)

theorem oneStep_sub_neg_of_super {n : ℕ} {Q : Set (Point n)} {ell L : ℝ}
    {v : Point n → ℝ}
    (hv : viscositySuper Q (fun H _ => -pucciPlus ell L (-H)) (fun _ => 0) v) :
    viscositySub Q (fun H _ => pucciPlus ell L H) (fun _ => 0) (fun p => -v p) := by
  intro p hp phi hphi ht
  have hneg : ContDiffAt ℝ 2 (fun z => -phi z) p := hphi.neg
  have htouch : touchBelow (fun z => -phi z) v p := by
    refine ⟨by have hh := ht.1; dsimp only at hh ⊢; linarith,?_⟩
    filter_upwards [ht.2] with q hq
    change -v q≤phi q at hq
    linarith
  have hh := hv p hp (fun z => -phi z) hneg htouch
  have htneg : timeD univ (fun z => -phi z) p = -timeD univ phi p := by
    simpa only [neg_one_mul] using harnack_timeD_const_mul hphi (-1)
  have hHneg : hessian (fun z => -phi z) p = -hessian phi p := by
    simpa only [neg_one_mul,neg_one_smul] using harnack_hessian_const_mul hphi (-1)
  rw [htneg,hHneg] at hh
  simp only [neg_neg] at hh
  change timeD univ phi p-pucciPlus ell L (hessian phi p)≤0
  linarith only [hh]

theorem oneStep_second_sub {n : ℕ} (hn : 0<n) {ell L : ℝ}
    (hell : 0<ell) (hL : ell≤L) {F : Sym n → ℝ}
    (hF : Continuous F) (hE : globalElliptic F ell L) (hC : ConcaveOn ℝ univ F)
    {u : Point n → ℝ} (hu : ContinuousOn u (unitClosed n))
    (hsol : viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u)
    (w : Point n →ᵇ ℝ) (heq : EqOn (w : Point n → ℝ) u (unitClosed n))
    {e : Space n} (he : ‖e‖=1) {h : ℝ} (hh : h≠0) (hhSmall : |h|<1/512) :
    viscositySub (autoOpen (0 : Space n) (3/4) 0)
      (fun H _ => pucciPlus ell L H) (fun _ => 0) (autoSecond w e h) := by
  have hbuf : (3/4:ℝ)+|h|<1 := by linarith only [hhSmall]
  have hsub := auto_second_sub hn hell hL (by norm_num : (0:ℝ)<3/4)
    (by norm_num : (3/4:ℝ)<1) hF hE hC hu hsol he hh hbuf
  apply viscositySub_eqOn_open (autoOpen_isOpen _ _ _) ?_ hsub
  intro p hp
  have hcenter := heq (unitOpen_subset_unitClosed
    (autoOpen_subset_unitOpen (by norm_num) (by norm_num) hp))
  have hplus := heq (unitOpen_subset_unitClosed
    (auto_spatial_translation_unit (by norm_num : (0:ℝ)<3/4) (by norm_num) he hbuf p hp))
  have hminus := heq (unitOpen_subset_unitClosed
    (auto_spatial_translation_unit (h := -h) (by norm_num : (0:ℝ)<3/4) (by norm_num) he
      (by simpa only [abs_neg] using hbuf) p hp))
  change w (p.1+h • e,p.2+0)=u (p.1+h • e,p.2+0) at hplus
  change w (p.1+(-h) • e,p.2+0)=u (p.1+(-h) • e,p.2+0) at hminus
  have hp' : w (p.1+h • e,p.2)=u (p.1+h • e,p.2) := by
    simpa only [add_zero] using hplus
  have hm' : w (p.1-h • e,p.2)=u (p.1-h • e,p.2) := by
    simpa only [add_zero,neg_smul,sub_eq_add_neg] using hminus
  unfold autoSecond
  rw [hp',hm',hcenter]

end Yau.LeafProofs.L05AutonomousAux

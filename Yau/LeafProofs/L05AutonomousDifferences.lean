import Yau.LeafProofs.L05JetCombinationRules
import Yau.LeafProofs.L05PucciHarnackTransport

noncomputable section
open Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

def autoClosed {n : ℕ} (c : Space n) (R T : ℝ) : Set (Point n) :=
  Metric.closedBall c R ×ˢ Icc (T-R^2) T

def autoOpen {n : ℕ} (c : Space n) (R T : ℝ) : Set (Point n) :=
  Metric.ball c R ×ˢ Ioo (T-R^2) T

def autoBack {n : ℕ} (c : Space n) (R T : ℝ) : Set (Point n) :=
  Metric.ball c R ×ˢ Ioc (T-R^2) T

def autoPucci {n : ℕ} (ell L : ℝ) (Q : Set (Point n)) (v : Point n → ℝ) : Prop :=
  viscositySub Q (fun H _ => pucciPlus ell L H) (fun _ => 0) v ∧
  viscositySuper Q (fun H _ => -pucciPlus ell L (-H)) (fun _ => 0) v

def autoSecond {n : ℕ} (u : Point n → ℝ) (e : Space n) (h : ℝ) (p : Point n) : ℝ :=
  (u (p.1+h • e,p.2)+u (p.1-h • e,p.2)-2*u p)/h^2

def autoTime {n : ℕ} (u : Point n → ℝ) (h : ℝ) (p : Point n) : ℝ :=
  (u p-u (p.1,p.2-h))/h

theorem autoOpen_isOpen {n : ℕ} (c : Space n) (R T : ℝ) : IsOpen (autoOpen c R T) :=
  Metric.isOpen_ball.prod isOpen_Ioo

/-- Translation uses the genuine test's actual first and second derivatives. -/
theorem auto_translate_jets {n : ℕ} {phi : Point n → ℝ} (p c : Point n)
    (hphi : ContDiffAt ℝ 2 phi (p+c)) :
    timeD univ (fun z => phi (z+c)) p=timeD univ phi (p+c) ∧
      hessian (fun z => phi (z+c)) p=hessian phi (p+c) := by
  have hshift : ContDiffAt ℝ 2 (fun z => phi (z+c)) p :=
    hphi.comp p (contDiffAt_id.add contDiffAt_const)
  constructor
  · rw [timeD_univ_eq_joint (hshift.differentiableAt (by norm_num)),
      timeD_univ_eq_joint (hphi.differentiableAt (by norm_num)),fderiv_comp_add_right]
  · rw [jet_hessian_eq_joint_at hshift,jet_hessian_eq_joint_at hphi]
    have hfirst : fderiv ℝ (fun z => phi (z+c))=fun z => fderiv ℝ phi (z+c) :=
      funext fun _ => fderiv_comp_add_right c
    rw [hfirst,fderiv_comp_add_right]

theorem auto_translate_sub {n : ℕ} {Q D : Set (Point n)} {F : Sym n → ℝ}
    {u : Point n → ℝ} (hu : viscositySub Q (fun H _ => F H) (fun _ => 0) u)
    (c : Point n) (hDQ : ∀ p∈D, p+c∈Q) :
    viscositySub D (fun H _ => F H) (fun _ => 0) (fun p => u (p+c)) := by
  intro p hp phi hphi ht
  let psi : Point n → ℝ := fun q => phi (q+(-c))
  have hphi' : ContDiffAt ℝ 2 phi ((p+c)+(-c)) := by simpa only [add_neg_cancel_right] using hphi
  have hpsi : ContDiffAt ℝ 2 psi (p+c) := hphi'.comp (p+c) (contDiffAt_id.add contDiffAt_const)
  have htend : Tendsto (fun q : Point n => q+(-c)) (𝓝 (p+c)) (𝓝 p) := by
    simpa only [id_eq,add_neg_cancel_right] using (continuous_id.add_const (-c)).tendsto (p+c)
  have htouch : touchAbove psi u (p+c) := by
    constructor
    · simpa only [psi,add_neg_cancel_right] using ht.1
    filter_upwards [htend ht.2] with q hq
    change u ((q+(-c))+c)≤phi (q+(-c)) at hq
    simpa only [psi,neg_add_cancel_right] using hq
  have htest := hu (p+c) (hDQ p hp) psi hpsi htouch
  have hj := auto_translate_jets (p+c) (-c) hphi'
  simpa only [psi,add_neg_cancel_right,hj.1,hj.2] using htest

theorem auto_translate_super {n : ℕ} {Q D : Set (Point n)} {F : Sym n → ℝ}
    {u : Point n → ℝ} (hu : viscositySuper Q (fun H _ => F H) (fun _ => 0) u)
    (c : Point n) (hDQ : ∀ p∈D, p+c∈Q) :
    viscositySuper D (fun H _ => F H) (fun _ => 0) (fun p => u (p+c)) := by
  intro p hp phi hphi ht
  let psi : Point n → ℝ := fun q => phi (q+(-c))
  have hphi' : ContDiffAt ℝ 2 phi ((p+c)+(-c)) := by simpa only [add_neg_cancel_right] using hphi
  have hpsi : ContDiffAt ℝ 2 psi (p+c) := hphi'.comp (p+c) (contDiffAt_id.add contDiffAt_const)
  have htend : Tendsto (fun q : Point n => q+(-c)) (𝓝 (p+c)) (𝓝 p) := by
    simpa only [id_eq,add_neg_cancel_right] using (continuous_id.add_const (-c)).tendsto (p+c)
  have htouch : touchBelow psi u (p+c) := by
    constructor
    · simpa only [psi,add_neg_cancel_right] using ht.1
    filter_upwards [htend ht.2] with q hq
    change phi (q+(-c))≤u ((q+(-c))+c) at hq
    simpa only [psi,neg_add_cancel_right] using hq
  have htest := hu (p+c) (hDQ p hp) psi hpsi htouch
  have hj := auto_translate_jets (p+c) (-c) hphi'
  simpa only [psi,add_neg_cancel_right,hj.1,hj.2] using htest

theorem auto_pucci_sub_scale {n : ℕ} {Q : Set (Point n)} {ell L a : ℝ}
    (hell : 0≤ell) (hL : ell≤L) (ha : 0<a) {w : Point n → ℝ}
    (hw : viscositySub Q (fun H _ => pucciPlus ell L H) (fun _ => 0) w) :
    viscositySub Q (fun H _ => pucciPlus ell L H) (fun _ => 0) (fun p => a*w p) := by
  intro p hp phi hphi ht
  let psi : Point n → ℝ := fun q => a⁻¹*phi q
  have hpsi : ContDiffAt ℝ 2 psi p := contDiffAt_const.mul hphi
  have htouch : touchAbove psi w p := by
    constructor
    · dsimp only [psi]
      rw [ht.1,← mul_assoc,inv_mul_cancel₀ ha.ne',one_mul]
    filter_upwards [ht.2] with q hq
    change a*w q≤phi q at hq
    change w q≤a⁻¹*phi q
    have hm := mul_le_mul_of_nonneg_left hq (inv_nonneg.mpr ha.le)
    simpa only [← mul_assoc,inv_mul_cancel₀ ha.ne',one_mul] using hm
  have hh := hw p hp psi hpsi htouch
  dsimp only [psi] at hh
  rw [harnack_timeD_const_mul hphi, harnack_hessian_const_mul hphi,
    harnack_plus_smul hell hL (inv_nonneg.mpr ha.le)] at hh
  have hmul := mul_le_mul_of_nonneg_left hh ha.le
  simpa only [mul_sub,← mul_assoc,mul_inv_cancel₀ ha.ne',one_mul,mul_zero] using hmul

theorem auto_pucci_super_neg {n : ℕ} {Q : Set (Point n)} {ell L : ℝ}
    {w : Point n → ℝ}
    (hw : viscositySub Q (fun H _ => pucciPlus ell L H) (fun _ => 0) w) :
    viscositySuper Q (fun H _ => -pucciPlus ell L (-H)) (fun _ => 0) (fun p => -w p) := by
  intro p hp phi hphi ht
  have hneg : ContDiffAt ℝ 2 (fun z => -phi z) p := hphi.neg
  have htouch : touchAbove (fun z => -phi z) w p := by
    refine ⟨by have hh := ht.1; dsimp only at hh ⊢; linarith,?_⟩
    filter_upwards [ht.2] with q hq
    change phi q≤-w q at hq
    change w q≤-phi q
    linarith
  have hh := hw p hp (fun z => -phi z) hneg htouch
  have htneg : timeD univ (fun z => -phi z) p = -timeD univ phi p := by
    simpa only [neg_one_mul] using harnack_timeD_const_mul hphi (-1)
  have hHneg : hessian (fun z => -phi z) p = -hessian phi p := by
    simpa only [neg_one_mul,neg_one_smul] using harnack_hessian_const_mul hphi (-1)
  rw [htneg,hHneg] at hh
  change 0≤timeD univ phi p-(-pucciPlus ell L (-hessian phi p))
  linarith only [hh]

theorem auto_pucci_deficit_super {n : ℕ} {Q : Set (Point n)} {ell L : ℝ}
    {w : Point n → ℝ}
    (hw : viscositySub Q (fun H _ => pucciPlus ell L H) (fun _ => 0) w) (M : ℝ) :
    viscositySuper Q (fun H _ => -pucciPlus ell L (-H)) (fun _ => 0) (fun p => M-w p) := by
  convert viscositySuper_add_const (auto_pucci_super_neg hw) M using 1
  funext p
  ring

theorem auto_difference_pucci {n : ℕ} {Q : Set (Point n)} {ell L : ℝ}
    {F : Sym n → ℝ} (hQ : IsOpen Q) (hell : 0≤ell) (hL : ell≤L)
    (hE : globalElliptic F ell L) {u v : Point n → ℝ}
    (hu : ContinuousOn u Q) (hv : ContinuousOn v Q)
    (hsolu : viscositySolution Q (fun H _ => F H) (fun _ => 0) u)
    (hsolv : viscositySolution Q (fun H _ => F H) (fun _ => 0) v)
    {a : ℝ} (ha : 0<a) :
    autoPucci ell L Q (fun p => a*(u p-v p)) := by
  have hs := jet_autonomous_difference_sub hQ hell hL hE hu hv hsolu.1 hsolv.2
  have hr := jet_autonomous_difference_sub hQ hell hL hE hv hu hsolv.1 hsolu.2
  refine ⟨auto_pucci_sub_scale hell hL ha hs,?_⟩
  have hsuper := auto_pucci_super_neg (auto_pucci_sub_scale hell hL ha hr)
  convert hsuper using 1
  funext p
  simp only [Pi.sub_apply]
  ring

theorem autoOpen_subset_unitOpen {n : ℕ} {R : ℝ} (hR : 0<R) (hR1 : R<1) :
    autoOpen (0 : Space n) R 0⊆unitOpen n := by
  intro p hp
  have hx : ‖p.1‖<R := by simpa only [Metric.mem_ball,dist_zero_right] using hp.1
  have ht : -R^2<p.2 ∧ p.2<0 := by simpa only [zero_sub,Set.mem_Ioo] using hp.2
  constructor
  · simpa only [Metric.mem_ball,dist_zero_right] using hx.trans hR1
  constructor
  · nlinarith only [ht.1,hR,hR1]
  · exact ht.2

theorem auto_spatial_translation_unit {n : ℕ} {R h : ℝ} {e : Space n}
    (hR : 0<R) (hR1 : R<1) (he : ‖e‖=1) (hbuf : R+|h|<1) :
    ∀ p∈autoOpen (0 : Space n) R 0, p+(h • e,0)∈unitOpen n := by
  intro p hp
  have hx : ‖p.1‖<R := by simpa only [Metric.mem_ball,dist_zero_right] using hp.1
  have ht : -R^2<p.2 ∧ p.2<0 := by simpa only [zero_sub,Set.mem_Ioo] using hp.2
  change p.1+h • e∈Metric.ball (0 : Space n) 1 ∧ p.2+0∈Ioo (-1:ℝ) 0
  constructor
  · have hn := norm_add_le p.1 (h • e)
    rw [norm_smul,Real.norm_eq_abs,he,mul_one] at hn
    have hh : ‖p.1+h • e‖<1 := by linarith only [hn,hx,hbuf]
    simpa only [Metric.mem_ball,dist_zero_right] using hh
  simp only [add_zero,mem_Ioo]
  exact ⟨by nlinarith only [ht.1,hR,hR1],ht.2⟩

theorem auto_time_translation_unit {n : ℕ} {R h : ℝ}
    (hR : 0<R) (hR1 : R<1) (hh : 0<h) (hbuf : R^2+h<1) :
    ∀ p∈autoOpen (0 : Space n) R 0, p+(0,-h)∈unitOpen n := by
  intro p hp
  have hx : ‖p.1‖<R := by simpa only [Metric.mem_ball,dist_zero_right] using hp.1
  have ht : -R^2<p.2 ∧ p.2<0 := by simpa only [zero_sub,Set.mem_Ioo] using hp.2
  change p.1+0∈Metric.ball (0 : Space n) 1 ∧ p.2+(-h)∈Ioo (-1:ℝ) 0
  constructor
  · simpa only [add_zero,Metric.mem_ball,dist_zero_right] using hx.trans hR1
  constructor <;> linarith only [ht.1,ht.2,hh,hbuf]

/-- Backward time increments satisfy BOTH literal Pucci inequalities. -/
theorem auto_time_pucci {n : ℕ} {ell L R : ℝ}
    (hell : 0<ell) (hL : ell≤L) (hR : 0<R) (hR1 : R<1)
    {F : Sym n → ℝ} (hE : globalElliptic F ell L) {u : Point n → ℝ}
    (hu : ContinuousOn u (unitClosed n))
    (hsol : viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u)
    {h : ℝ} (hh : 0<h) (hbuf : R^2+h<1) :
    autoPucci ell L (autoOpen (0 : Space n) R 0) (autoTime u h) := by
  let Q := autoOpen (0 : Space n) R 0
  have hQ := autoOpen_isOpen (0 : Space n) R 0
  have hsub : Q⊆unitOpen n := autoOpen_subset_unitOpen hR hR1
  have hmap := auto_time_translation_unit (n := n) hR hR1 hh hbuf
  have huQ : ContinuousOn u Q := hu.mono fun _ hp => unitOpen_subset_unitClosed (hsub hp)
  have hvQ : ContinuousOn (fun p => u (p+(0,-h))) Q :=
    hu.comp (continuous_id.add_const ((0,-h) : Point n)).continuousOn
      (fun p hp => unitOpen_subset_unitClosed (hmap p hp))
  have hsolu : viscositySolution Q (fun H _ => F H) (fun _ => 0) u :=
    ⟨viscositySub_mono_domain hsol.1 hsub,viscositySuper_mono_domain hsol.2 hsub⟩
  have hsolv : viscositySolution Q (fun H _ => F H) (fun _ => 0) (fun p => u (p+(0,-h))) :=
    ⟨auto_translate_sub hsol.1 _ hmap,auto_translate_super hsol.2 _ hmap⟩
  have hd := auto_difference_pucci hQ hell.le hL hE huQ hvQ hsolu hsolv (inv_pos.mpr hh)
  convert hd using 1
  funext p
  rcases p with ⟨x,t⟩
  dsimp only [autoTime,Prod.mk_add_mk]
  simp only [add_zero,sub_eq_add_neg,div_eq_mul_inv]
  ring

/-- Concavity gives the spatial second-difference SUBsolution; no opposite sign is asserted. -/
theorem auto_second_sub {n : ℕ} (hn : 0<n) {ell L R : ℝ}
    (hell : 0<ell) (hL : ell≤L) (hR : 0<R) (hR1 : R<1)
    {F : Sym n → ℝ} (hF : Continuous F) (hE : globalElliptic F ell L)
    (hC : ConcaveOn ℝ univ F) {u : Point n → ℝ}
    (hu : ContinuousOn u (unitClosed n))
    (hsol : viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u)
    {e : Space n} (he : ‖e‖=1) {h : ℝ} (hh : h≠0) (hbuf : R+|h|<1) :
    viscositySub (autoOpen (0 : Space n) R 0)
      (fun H _ => pucciPlus ell L H) (fun _ => 0) (autoSecond u e h) := by
  let Q := autoOpen (0 : Space n) R 0
  have hQ := autoOpen_isOpen (0 : Space n) R 0
  have hsub : Q⊆unitOpen n := autoOpen_subset_unitOpen hR hR1
  have hplus := auto_spatial_translation_unit (n := n) hR hR1 he hbuf
  have hminus := auto_spatial_translation_unit (n := n) (h := -h) hR hR1 he
    (by simpa only [abs_neg] using hbuf)
  have huQ : ContinuousOn u Q := hu.mono fun _ hp => unitOpen_subset_unitClosed (hsub hp)
  have hup : ContinuousOn (fun p => u (p+(h • e,0))) Q :=
    hu.comp (continuous_id.add_const ((h • e,0) : Point n)).continuousOn
      (fun p hp => unitOpen_subset_unitClosed (hplus p hp))
  have hum : ContinuousOn (fun p => u (p+((-h) • e,0))) Q :=
    hu.comp (continuous_id.add_const (((-h) • e,0) : Point n)).continuousOn
      (fun p hp => unitOpen_subset_unitClosed (hminus p hp))
  have hupsub := auto_translate_sub hsol.1 _ hplus
  have humsub := auto_translate_sub hsol.1 _ hminus
  have hmean := jet_autonomous_convex_combination_sub hQ hell.le hL hE hC hup hum hupsub humsub
    (show (1/2:ℝ)∈Icc 0 1 from ⟨by norm_num,by norm_num⟩)
  have hmeancont : ContinuousOn (fun p => (1/2:ℝ)*u (p+(h • e,0))+
      (1-1/2:ℝ)*u (p+((-h) • e,0))) Q :=
    (continuousOn_const.mul hup).add (continuousOn_const.mul hum)
  have hdiff := jet_autonomous_difference_sub hQ hell.le hL hE hmeancont huQ hmean
    (viscositySuper_mono_domain hsol.2 hsub)
  have hscale := auto_pucci_sub_scale hell.le hL (show 0<2/h^2 from div_pos (by norm_num) (sq_pos_of_ne_zero hh)) hdiff
  convert hscale using 1
  funext p
  rcases p with ⟨x,t⟩
  dsimp only [autoSecond,Pi.sub_apply,Prod.mk_add_mk]
  simp only [add_zero,neg_smul,sub_eq_add_neg]
  ring

end Yau.LeafProofs.L05AutonomousAux

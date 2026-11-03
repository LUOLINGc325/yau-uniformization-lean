import Yau.LeafProofs.L05AutonomousHarnackConsequences

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

def autoScale {n : ℕ} (c : Space n) (R T : ℝ) (z : Point n) : Point n :=
  harnackAffine c R (T-R^2) (R^2) z

theorem autoScale_apply {n : ℕ} (c : Space n) (R T : ℝ) (z : Point n) :
    autoScale c R T z=(c+R • z.1,T+R^2*z.2) := by
  rw [autoScale,harnack_affine_apply]
  congr 1
  ring

theorem autoScale_comp {n : ℕ} (c : Space n) (R T r : ℝ) (z : Point n) :
    autoScale c R T (autoScale 0 r 0 z)=autoScale c (R*r) T z := by
  simp only [autoScale_apply,zero_add,smul_smul,Prod.mk.injEq]
  constructor
  · trivial
  · ring

theorem autoScale_closed_image {n : ℕ} (c : Space n) {R : ℝ} (hR : 0<R) (T : ℝ) :
    autoScale c R T '' unitClosed n=autoClosed c R T := by
  have hh := harnack_affine_image_closed c (a := T-R^2) hR (sq_pos_of_pos hR)
  change harnackAffine c R (T-R^2) (R^2) '' unitClosed n=autoClosed c R T
  simpa only [harnackClosed,autoClosed,sub_add_cancel] using hh

theorem autoScale_open_image {n : ℕ} (c : Space n) {R : ℝ} (hR : 0<R) (T : ℝ) :
    autoScale c R T '' unitOpen n=autoOpen c R T := by
  have hh := harnack_affine_image_open c (a := T-R^2) hR (sq_pos_of_pos hR)
  change harnackAffine c R (T-R^2) (R^2) '' unitOpen n=autoOpen c R T
  simpa only [harnackOpen,autoOpen,sub_add_cancel] using hh

theorem autoScale_closed_maps {n : ℕ} (c : Space n) {R : ℝ} (hR : 0<R) (T : ℝ) :
    MapsTo (autoScale c R T) (unitClosed n) (autoClosed c R T) :=
  mapsTo_iff_image_subset.mpr (autoScale_closed_image c hR T).subset

theorem autoScale_open_maps {n : ℕ} (c : Space n) {R : ℝ} (hR : 0<R) (T : ℝ) :
    MapsTo (autoScale c R T) (unitOpen n) (autoOpen c R T) :=
  mapsTo_iff_image_subset.mpr (autoScale_open_image c hR T).subset

theorem autoScale_quarter_image {n : ℕ} (c : Space n) {R : ℝ} (hR : 0<R) (T : ℝ) :
    autoScale c R T '' autoClosed 0 (1/4) 0=autoClosed c (R/4) T := by
  rw [← autoScale_closed_image (0 : Space n) (by norm_num : (0 : ℝ)<1/4) 0,← Set.image_comp]
  have heq : autoScale c R T ∘ autoScale 0 (1/4) 0=autoScale c (R/4) T := by
    funext z
    simpa only [Function.comp_def,div_eq_mul_inv,one_mul] using autoScale_comp c R T (1/4) z
  rw [heq,autoScale_closed_image c (div_pos hR (by norm_num)) T]

/-- Genuine space-time pullback of the two native Pucci inequalities. -/
theorem auto_pucci_rescale {n : ℕ} {ell L : ℝ} (hell : 0<ell) (hL : ell≤L)
    (c : Space n) {R T : ℝ} (hR : 0<R) {w : Point n → ℝ}
    (hP : autoPucci ell L (autoOpen c R T) w) :
    autoPucci ell L (unitOpen n) (fun z => w (autoScale c R T z)) := by
  have hsub := harnack_sub_affine_pullback hell.le hL hP.1 c hR (sq_pos_of_pos hR)
    (h := 1) zero_lt_one (autoScale_open_maps c hR T)
  have hsuper := harnack_super_affine_pullback hell.le hL hP.2 c hR (sq_pos_of_pos hR)
    (h := 1) zero_lt_one (autoScale_open_maps c hR T)
  have hsq : R^2≠0 := (sq_pos_of_pos hR).ne'
  constructor
  · simpa only [autoScale,div_self hsq,one_mul,div_one,mul_zero] using hsub
  · simpa only [autoScale,harnackPucciMinus,div_self hsq,one_mul,div_one,mul_zero] using hsuper

/-- The same contraction constant works on every translated and parabolically scaled cylinder. -/
theorem auto_pucci_scaled_quarter_contraction {n : ℕ} (hn : 0<n) {ell L : ℝ}
    (hell : 0<ell) (hL : ell≤L) :
    ∃ theta : ℝ, 0<theta ∧ theta<1 ∧ ∀ (c : Space n) (R T : ℝ), 0<R →
      ∀ (w : Point n → ℝ) (m M : ℝ), ContinuousOn w (autoClosed c R T) →
      (∀ z∈autoClosed c R T, m≤w z ∧ w z≤M) →
      autoPucci ell L (autoOpen c R T) w →
      ∀ z∈autoClosed c (R/4) T, ∀ q∈autoClosed c (R/4) T,
        w z-w q≤(1-theta)*(M-m) := by
  obtain ⟨theta,ht,ht1,hstep⟩ := auto_pucci_quarter_contraction hn hell hL
  refine ⟨theta,ht,ht1,?_⟩
  intro c R T hR w m M hw hb hP z hz q hq
  rw [← autoScale_quarter_image c hR T] at hz hq
  obtain ⟨z',hz',rfl⟩ := hz
  obtain ⟨q',hq',rfl⟩ := hq
  have hcont : Continuous (autoScale c R T) := (harnack_affine_contDiff c R (T-R^2) (R^2)).continuous
  exact hstep (fun y => w (autoScale c R T y)) m M
    (hw.comp hcont.continuousOn (autoScale_closed_maps c hR T))
    (fun y hy => hb _ (autoScale_closed_maps c hR T hy))
    (auto_pucci_rescale hell hL c hR hP) z' hz' q' hq'

end Yau.LeafProofs.L05AutonomousAux

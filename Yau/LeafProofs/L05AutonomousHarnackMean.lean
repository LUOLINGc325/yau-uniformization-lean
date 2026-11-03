import Yau.LeafProofs.L05AutonomousHarnackScaling

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

def autoEarly {n : ℕ} (c : Space n) (R T : ℝ) : Set (Point n) :=
  harnackOpen c (R/4) (T-3*R^2/4) (R^2/4)

theorem autoEarly_eq {n : ℕ} (c : Space n) (R T : ℝ) :
    autoEarly c R T=Metric.ball c (R/4) ×ˢ Ioo (T-3*R^2/4) (T-R^2/2) := by
  unfold autoEarly harnackOpen
  rw [show T-3*R^2/4+R^2/4=T-R^2/2 by ring]

theorem autoEarly_subset_open {n : ℕ} (c : Space n) {R : ℝ} (hR : 0< R) (T : ℝ) :
    autoEarly c R T⊆autoOpen c R T := by
  rw [autoEarly_eq]
  intro z hz
  refine ⟨Metric.ball_subset_ball (by linarith : R/4≤ R) hz.1,?_⟩
  change T-R^2< z.2 ∧ z.2< T
  have ht : T-3*R^2/4< z.2 ∧ z.2< T-R^2/2 := hz.2
  have hs : 0< R^2 := sq_pos_of_pos hR
  constructor <;> linarith only [ht.1,ht.2,hs]

/-- Actual affine change of variables cancels the Jacobian from the normalized mean. -/
theorem autoLpMean_affine_open {n : ℕ} (c : Space n) {R a T : ℝ}
    (hR : 0< R) (hT : 0< T) (p : ℝ) (v : Point n → ℝ) :
    autoLpMean (unitOpen n) p (fun z => v (harnackAffine c R a T z))=
      autoLpMean (harnackOpen c R a T) p v := by
  have hi := harnack_integral_affine_open c (a := a) hR hT (fun y => (v y)^p)
  have hv := harnack_integral_affine_open c (a := a) hR hT (fun _ => (1 : ℝ))
  have hmu : ((volume : Measure (Point n)) (unitOpen n)).toReal=
      (harnackAffineJacobian n R T)⁻¹*((volume : Measure (Point n)) (harnackOpen c R a T)).toReal := by
    simpa only [setIntegral_const,smul_eq_mul,mul_one,measureReal_def] using hv
  unfold autoLpMean
  rw [hi,hmu]
  congr 1
  have hj := (harnack_affineJacobian_pos (n := n) hR hT).ne'
  exact mul_div_mul_left _ _ (inv_ne_zero hj)

theorem autoScale_early_comp {n : ℕ} (c : Space n) (R T : ℝ) (z : Point n) :
    autoScale c R T (harnackAffine 0 (1/4) (-3/4) (1/4) z)=
      harnackAffine c (R/4) (T-3*R^2/4) (R^2/4) z := by
  simp only [autoScale_apply,harnack_affine_apply,zero_add,smul_smul,div_eq_mul_inv,one_mul,Prod.mk.injEq]
  constructor
  · trivial
  · ring

theorem autoLpMean_scale_early {n : ℕ} (c : Space n) {R : ℝ} (hR : 0< R) (T p : ℝ)
    (v : Point n → ℝ) :
    autoLpMean (harnackQminus n) p (fun z => v (autoScale c R T z))=
      autoLpMean (autoEarly c R T) p v := by
  have hsmall := autoLpMean_affine_open (0 : Space n) (a := -3/4)
    (by norm_num : (0 : ℝ)< 1/4) (by norm_num : (0 : ℝ)< 1/4) p (fun y => v (autoScale c R T y))
  have hQ : harnackOpen (0 : Space n) (1/4) (-3/4) (1/4)=harnackQminus n := by
    simp only [harnackOpen,harnackQminus]
    norm_num
  rw [hQ] at hsmall
  rw [← hsmall]
  have heq : (fun z => v (autoScale c R T (harnackAffine 0 (1/4) (-3/4) (1/4) z)))=
      (fun z => v (harnackAffine c (R/4) (T-3*R^2/4) (R^2/4) z)) :=
    funext fun z => congrArg v (autoScale_early_comp c R T z)
  rw [heq]
  exact autoLpMean_affine_open c (div_pos hR (by norm_num))
    (div_pos (sq_pos_of_pos hR) (by norm_num)) p v

/-- Normalized weak Harnack at the genuine closed top, derived by continuity. -/
theorem auto_weak_harnack_closed_top {n : ℕ} (hn : 0< n) {ell L : ℝ}
    (hell : 0< ell) (hL : ell≤ L) :
    ∃ p C : ℝ, 0< p ∧ p< 1 ∧ 0< C ∧ ∀ v : Point n → ℝ,
      ContinuousOn v (unitClosed n) → (∀ z∈unitClosed n, 0≤ v z) →
      viscositySuper (unitOpen n) (fun H _ => -pucciPlus ell L (-H)) (fun _ => 0) v →
      ∀ z∈closure (harnackQplus n), autoLpMean (harnackQminus n) p v≤ C*v z := by
  obtain ⟨p,C,hp,hp1,hC,hWH⟩ := auto_weak_harnack_homogeneous hn hell hL
  refine ⟨p,C,hp,hp1,hC,?_⟩
  intro v hv hv0 hSuper z hz
  have hclosed : IsClosed (unitClosed n) :=
    ((isCompact_closedBall (0 : Space n) 1).prod isCompact_Icc).isClosed
  have hsub : closure (harnackQplus n)⊆unitClosed n :=
    closure_minimal harnack_qplus_subset_unitClosed hclosed
  exact le_on_closure (hWH v hv hv0 hSuper) continuousOn_const
    ((continuousOn_const.mul hv).mono hsub) hz

/-- The actual scaled early-slab mean is controlled at the closed top centre. -/
theorem auto_weak_harnack_scaled_top {n : ℕ} (hn : 0< n) {ell L : ℝ}
    (hell : 0< ell) (hL : ell≤ L) :
    ∃ p C : ℝ, 0< p ∧ p< 1 ∧ 0< C ∧ ∀ (c : Space n) (R T : ℝ), 0< R →
      ∀ v : Point n → ℝ, ContinuousOn v (autoClosed c R T) →
      (∀ z∈autoClosed c R T, 0≤ v z) →
      viscositySuper (autoOpen c R T) (fun H _ => -pucciPlus ell L (-H)) (fun _ => 0) v →
      autoLpMean (autoEarly c R T) p v≤ C*v (c,T) := by
  obtain ⟨p,C,hp,hp1,hC,hWH⟩ := auto_weak_harnack_closed_top hn hell hL
  refine ⟨p,C,hp,hp1,hC,?_⟩
  intro c R T hR v hv hv0 hSuper
  let u : Point n → ℝ := fun z => v (autoScale c R T z)
  have hu : ContinuousOn u (unitClosed n) := hv.comp
    (harnack_affine_contDiff c R (T-R^2) (R^2)).continuous.continuousOn (autoScale_closed_maps c hR T)
  have hu0 : ∀ z∈unitClosed n, 0≤ u z := fun z hz => hv0 _ (autoScale_closed_maps c hR T hz)
  have hs := harnack_super_affine_pullback hell.le hL hSuper c hR (sq_pos_of_pos hR)
    (h := 1) zero_lt_one (autoScale_open_maps c hR T)
  have huSuper : viscositySuper (unitOpen n) (fun H _ => -pucciPlus ell L (-H)) (fun _ => 0) u := by
    simpa only [u,autoScale,harnackPucciMinus,div_self (sq_pos_of_pos hR).ne',one_mul,div_one,mul_zero] using hs
  have hcenter : ((0 : Space n),(0 : ℝ))∈closure (harnackQplus n) := by
    rw [harnackQplus,closure_prod_eq,closure_ball (0 : Space n) (by norm_num),
      closure_Ioo (by norm_num : (-1/4 : ℝ)≠0)]
    simp only [mem_prod,Metric.mem_closedBall,dist_self,mem_Icc]
    norm_num
  have hh := hWH u hu hu0 huSuper (0,0) hcenter
  change autoLpMean (harnackQminus n) p (fun z => v (autoScale c R T z))≤ C*v (autoScale c R T (0,0)) at hh
  rw [autoLpMean_scale_early c hR T p v,autoScale_apply] at hh
  simpa only [smul_zero,add_zero,mul_zero] using hh

/-- Literal early-slab volume, including the actual 2n+2 parabolic scale. -/
theorem autoEarly_volume {n : ℕ} (c : Space n) {R : ℝ} (hR : 0< R) (T : ℝ) :
    harnackMu (autoEarly c R T)=R^(2*n+2)*harnackMu (harnackQminus n) := by
  rw [autoEarly_eq,harnackMu,Measure.volume_eq_prod,Measure.prod_prod]
  have hBall := (volume : Measure (Space n)).addHaar_ball_of_pos c (div_pos hR (by norm_num : (0 : ℝ)< 4))
  rw [complexVector_finrank_real] at hBall
  have hLen : (T-R^2/2)-(T-3*R^2/4)=R^2/4 := by ring
  rw [Real.volume_Ioo,hLen,hBall,ENNReal.toReal_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg (div_nonneg hR.le (by norm_num)) _),
    ENNReal.toReal_ofReal (div_nonneg (sq_nonneg R) (by norm_num)),harnack_qminus_volume]
  rw [pow_add,pow_succ]
  simp only [div_pow,one_pow]
  ring

theorem autoEarly_mu_pos {n : ℕ} (c : Space n) {R : ℝ} (hR : 0< R) (T : ℝ) :
    0< harnackMu (autoEarly c R T) := by
  rw [autoEarly_volume c hR T]
  exact mul_pos (pow_pos hR _) (harnack_qminus_mu_pos n)

theorem autoEarly_isOpen {n : ℕ} (c : Space n) (R T : ℝ) : IsOpen (autoEarly c R T) :=
  Metric.isOpen_ball.prod isOpen_Ioo

theorem autoEarly_measure_ne_top {n : ℕ} (c : Space n) (R T : ℝ) :
    (volume : Measure (Point n)) (autoEarly c R T)≠⊤ := by
  apply ne_of_lt
  apply lt_of_le_of_lt (measure_mono (show autoEarly c R T⊆
      Metric.closedBall c (R/4) ×ˢ Icc (T-3*R^2/4) (T-R^2/2) from by
        rw [autoEarly_eq]
        exact Set.prod_mono Metric.ball_subset_closedBall Ioo_subset_Icc_self))
  exact ((isCompact_closedBall c (R/4)).prod isCompact_Icc).measure_lt_top

end Yau.LeafProofs.L05AutonomousAux

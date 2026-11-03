import Yau.LeafProofs.L05ABPAlgebra

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

def abpClosed (n : ℕ) (R a b : ℝ) : Set (Point n) :=
  Metric.closedBall 0 R ×ˢ Set.Icc a b

def abpOpen (n : ℕ) (R a b : ℝ) : Set (Point n) :=
  Metric.ball 0 R ×ˢ Set.Ioo a b

def abpBoundary (n : ℕ) (R a b : ℝ) : Set (Point n) :=
  (Metric.closedBall 0 R ×ˢ ({a} : Set ℝ)) ∪
    (Metric.sphere 0 R ×ˢ Set.Icc a b)

def spatialGrad {n : ℕ} (u : Point n → ℝ) (z : Point n) : Space n :=
  (InnerProductSpace.toDual ℝ (Space n)).symm (spatialD u z)

theorem spatialGrad_inner {n : ℕ} (u : Point n → ℝ) (z : Point n) (v : Space n) :
    inner ℝ (spatialGrad u z) v = spatialD u z v := InnerProductSpace.toDual_symm_apply

def pastSupports {n : ℕ} (R a : ℝ) (u : Point n → ℝ)
    (z : Point n) (xi : Space n) : Prop :=
  ∀ y ∈ Metric.closedBall (0 : Space n) R, ∀ s ∈ Set.Icc a z.2,
    u (y,s) ≤ u z+inner ℝ xi (y-z.1)

def smoothContact {n : ℕ} (R a b : ℝ) (u : Point n → ℝ) : Set (Point n) :=
  {z | z ∈ abpOpen n R a b ∧ pastSupports R a u z (spatialGrad u z)}

def contactMap {n : ℕ} (u : Point n → ℝ) (z : Point n) : Point n :=
  (spatialGrad u z,u z-inner ℝ z.1 (spatialGrad u z))

def contactCone (n : ℕ) (m : ℝ) : Set (Point n) :=
  Metric.ball (0 : Space n) (m/4) ×ˢ Set.Ioo (m/4) (3*m/4)

def abpKappa (n : ℕ) : ℝ :=
  (volume (Metric.ball (0 : Space n) 1)).toReal/(2*4^(2*n))

def abpC (n : ℕ) (ell : ℝ) : ℝ := 1+(abpKappa n)⁻¹*(2/ell)^(2*n)

theorem abpKappa_pos (n : ℕ) : 0 < abpKappa n := by
  unfold abpKappa
  apply div_pos
  · apply ENNReal.toReal_pos
    · exact ne_of_gt (Metric.measure_ball_pos volume (0 : Space n) (by norm_num : (0:ℝ)<1))
    · exact ne_of_lt measure_ball_lt_top
  · positivity

theorem abpC_pos (n : ℕ) {ell : ℝ} (hell : 0 < ell) : 0 < abpC n ell := by
  unfold abpC
  have hk := abpKappa_pos n
  positivity

theorem spatialD_eq_joint {n : ℕ} {u : Point n → ℝ} {z : Point n}
    (hu : DifferentiableAt ℝ u z) :
    spatialD u z = (fderiv ℝ u z).comp (ContinuousLinearMap.inl ℝ (Space n) ℝ) := by
  have hh : HasFDerivAt (fun x : Space n => (x,z.2))
      (ContinuousLinearMap.inl ℝ (Space n) ℝ) z.1 := by
    simpa only [ContinuousLinearMap.inl_apply,Prod.mk_add_mk,add_zero,zero_add] using
      ((ContinuousLinearMap.inl ℝ (Space n) ℝ).hasFDerivAt).add_const ((0,z.2) : Point n)
  exact (hu.hasFDerivAt.comp z.1 hh).fderiv

theorem spatialD_smooth {n : ℕ} {u : Point n → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (spatialD u) := by
  have he : spatialD u = fun z => (fderiv ℝ u z).comp
      (ContinuousLinearMap.inl ℝ (Space n) ℝ) := by
    funext z
    exact spatialD_eq_joint (hu.differentiable (by simp) z)
  rw [he]
  exact (hu.fderiv_right (by simp)).clm_comp contDiff_const

theorem spatialGrad_smooth {n : ℕ} {u : Point n → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (spatialGrad u) :=
  (InnerProductSpace.toDual ℝ (Space n)).symm.toContinuousLinearEquiv.contDiff.comp
    (spatialD_smooth hu)

theorem contactMap_smooth {n : ℕ} {u : Point n → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (contactMap u) := by
  exact (spatialGrad_smooth hu).prodMk
    (hu.sub (contDiff_fst.inner ℝ (spatialGrad_smooth hu)))

theorem pastSupports_iff_unitInterval {n : ℕ} {R a : ℝ} {u : Point n → ℝ}
    {z : Point n} {xi : Space n} (ha : a ≤ z.2) :
    pastSupports R a u z xi ↔
      ∀ y ∈ Metric.closedBall (0 : Space n) R, ∀ θ ∈ Set.Icc (0 : ℝ) 1,
        u (y,a+θ*(z.2-a)) ≤ u z+inner ℝ xi (y-z.1) := by
  constructor
  · intro h y hy θ hθ
    apply h y hy
    constructor <;> nlinarith [hθ.1,hθ.2]
  · intro h y hy s hs
    by_cases ht : z.2 = a
    · have he : s = a := le_antisymm (by simpa only [ht] using hs.2) hs.1
      have hh := h y hy 0 ⟨le_rfl,zero_le_one⟩
      simpa only [zero_mul,add_zero,he] using hh
    · have ht0 : 0 < z.2-a := sub_pos.mpr (lt_of_le_of_ne ha (Ne.symm ht))
      have hθ : (s-a)/(z.2-a) ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨div_nonneg (sub_nonneg.mpr hs.1) ht0.le,
          (div_le_one ht0).2 (sub_le_sub_right hs.2 a)⟩
      have hh := h y hy ((s-a)/(z.2-a)) hθ
      have he : a+(s-a)/(z.2-a)*(z.2-a) = s := by
        rw [div_mul_cancel₀ _ ht0.ne']; ring
      simpa only [he] using hh

theorem smoothContact_measurable {n : ℕ} {R a b : ℝ} {u : Point n → ℝ}
    (hu : ContDiff ℝ ∞ u) : MeasurableSet (smoothContact R a b u) := by
  let S : Set (Point n) := {z | ∀ y ∈ Metric.closedBall (0 : Space n) R,
    ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      u (y,a+θ*(z.2-a)) ≤ u z+inner ℝ (spatialGrad u z) (y-z.1)}
  have hS : IsClosed S := by
    dsimp only [S]
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun y => isClosed_iInter fun _hy =>
      isClosed_iInter fun θ => isClosed_iInter fun _hθ => ?_
    apply isClosed_le
    · exact hu.continuous.comp (continuous_const.prodMk
        (continuous_const.add (continuous_const.mul (continuous_snd.sub continuous_const))))
    · exact hu.continuous.add
        ((spatialGrad_smooth hu).continuous.inner (continuous_const.sub continuous_fst))
  have he : smoothContact R a b u = abpOpen n R a b ∩ S := by
    ext z
    constructor
    · rintro ⟨hz,hs⟩
      exact ⟨hz,(pastSupports_iff_unitInterval hz.2.1.le).1 hs⟩
    · rintro ⟨hz,hs⟩
      exact ⟨hz,(pastSupports_iff_unitInterval hz.2.1.le).2 hs⟩
  rw [he]
  exact (Metric.isOpen_ball.prod isOpen_Ioo).measurableSet.inter hS.measurableSet

theorem support_slope_eq_spatialGrad {n : ℕ} {R : ℝ} {u : Point n → ℝ}
    {z : Point n} {xi : Space n} (hu : DifferentiableAt ℝ (fun y => u (y,z.2)) z.1)
    (hz : z.1 ∈ Metric.ball 0 R)
    (hs : ∀ y ∈ Metric.closedBall 0 R, u (y,z.2) ≤ u z+inner ℝ xi (y-z.1)) :
    xi = spatialGrad u z := by
  have hm : IsLocalMax (fun y => u (y,z.2)-inner ℝ xi y) z.1 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
    have hh := hs y (Metric.ball_subset_closedBall hy)
    rw [inner_sub_right] at hh
    linarith
  have hd := hm.fderiv_eq_zero
  change fderiv ℝ (fun y => u (y,z.2)-(innerSL ℝ xi) y) z.1 = 0 at hd
  rw [fderiv_fun_sub hu (innerSL ℝ xi).differentiableAt] at hd
  simp only [ContinuousLinearMap.fderiv] at hd
  apply (InnerProductSpace.toDual ℝ (Space n)).injective
  rw [spatialGrad,LinearIsometryEquiv.apply_symm_apply]
  exact (sub_eq_zero.mp hd).symm

/-- The first contact is obtained by minimizing time on a compact level set.
This avoids an unverified time-dependent maximum selection. -/
theorem contactCone_subset_image {n : ℕ} {R a b : ℝ} {u : Point n → ℝ}
    (_hR : 0 < R) (hR1 : R ≤ 1) (_hab : a < b) (hu : ContDiff ℝ ∞ u)
    (hboundary : ∀ z ∈ abpBoundary n R a b, u z ≤ 0)
    {z0 : Point n} (hz0 : z0 ∈ abpClosed n R a b) (_hm : 0 < u z0) :
    contactCone n (u z0) ⊆ contactMap u '' smoothContact R a b u := by
  rintro ⟨xi,height⟩ hpar
  have hxi : ‖xi‖ < u z0/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hpar.1
  have hinner (x : Space n) (hx : x ∈ Metric.closedBall 0 R) :
      |inner ℝ xi x| < u z0/4 := by
    have hxR : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
    have hx1 : ‖x‖ ≤ 1 := hxR.trans hR1
    have hh := (abs_real_inner_le_norm xi x).trans (mul_le_mul_of_nonneg_left hx1 (norm_nonneg xi))
    have hh' : |inner ℝ xi x| ≤ ‖xi‖ := by simpa only [mul_one] using hh
    exact hh'.trans_lt hxi
  let F : Point n → ℝ := fun z => u z-inner ℝ xi z.1
  have hF : Continuous F := hu.continuous.sub ((innerSL ℝ xi).continuous.comp continuous_fst)
  have hbottom (x : Space n) (hx : x ∈ Metric.closedBall 0 R) : F (x,a) < height := by
    have hh := hboundary (x,a) (Or.inl ⟨hx,rfl⟩)
    have hi := hinner x hx
    have hp := hpar.2.1
    dsimp only [F]
    linarith [neg_le_abs (inner ℝ xi x)]
  have htop : height < F z0 := by
    have hi := hinner z0.1 hz0.1
    have hp := hpar.2.2
    dsimp only [F]
    linarith [le_abs_self (inner ℝ xi z0.1)]
  let S : Set (Point n) := abpClosed n R a b ∩ {z | F z = height}
  have hS : IsCompact S := ((ProperSpace.isCompact_closedBall (0 : Space n) R).prod isCompact_Icc).inter_right
    (isClosed_eq hF continuous_const)
  have hSnon : S.Nonempty := by
    have ht : ContinuousOn (fun t => F (z0.1,t)) (Set.Icc a z0.2) :=
      (hF.comp (continuous_const.prodMk continuous_id)).continuousOn
    obtain ⟨s,hs,he⟩ := intermediate_value_Icc hz0.2.1 ht ⟨(hbottom z0.1 hz0.1).le,htop.le⟩
    exact ⟨(z0.1,s),⟨hz0.1,hs.1,hs.2.trans hz0.2.2⟩,he⟩
  obtain ⟨z,hz,hmin⟩ := hS.exists_isMinOn hSnon continuous_snd.continuousOn
  have hzF : F z = height := hz.2
  have hza : a < z.2 := by
    by_contra h
    have he : z.2 = a := le_antisymm (le_of_not_gt h) hz.1.2.1
    have hh := hbottom z.1 hz.1.1
    have heF : F (z.1,a) = height := by simpa only [← he] using hzF
    linarith
  have hsupport (y : Space n) (hy : y ∈ Metric.closedBall 0 R)
      (s : ℝ) (hs : s ∈ Set.Icc a z.2) : F (y,s) ≤ height := by
    by_contra h
    have hlt : height < F (y,s) := lt_of_not_ge h
    have ht : ContinuousOn (fun t => F (y,t)) (Set.Icc a s) :=
      (hF.comp (continuous_const.prodMk continuous_id)).continuousOn
    obtain ⟨r,hr,he⟩ := intermediate_value_Ioo hs.1 ht ⟨hbottom y hy,hlt⟩
    have hrS : (y,r) ∈ S := ⟨⟨hy,hr.1.le,(hr.2.trans_le hs.2).le.trans hz.1.2.2⟩,he⟩
    have hmin' := hmin hrS
    exact (not_lt_of_ge hmin') (hr.2.trans_le hs.2)
  have hzball : z.1 ∈ Metric.ball 0 R := by
    have hzle : ‖z.1‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1.1
    by_contra h
    have he : ‖z.1‖ = R := le_antisymm hzle (le_of_not_gt (by simpa only [Metric.mem_ball,dist_zero_right] using h))
    have hh := hboundary z (Or.inr ⟨by simpa only [Metric.mem_sphere,dist_zero_right] using he,hz.1.2⟩)
    have hi := hinner z.1 hz.1.1
    have heF := hzF
    have hp := hpar.2.1
    dsimp only [F] at heF
    linarith [neg_le_abs (inner ℝ xi z.1)]
  have hzb : z.2 < b := by
    have ht : ContinuousOn (fun t => F (z0.1,t)) (Set.Icc a z0.2) :=
      (hF.comp (continuous_const.prodMk continuous_id)).continuousOn
    obtain ⟨s,hs,he⟩ := intermediate_value_Ioo hz0.2.1 ht ⟨hbottom z0.1 hz0.1,htop⟩
    have hsS : (z0.1,s) ∈ S := ⟨⟨hz0.1,hs.1.le,(hs.2.trans_le hz0.2.2).le⟩,he⟩
    exact (hmin hsS).trans_lt (hs.2.trans_le hz0.2.2)
  have hsl : ∀ y ∈ Metric.closedBall 0 R,
      u (y,z.2) ≤ u z+inner ℝ xi (y-z.1) := by
    intro y hy
    have hh := hsupport y hy z.2 ⟨hza.le,le_rfl⟩
    have he := hzF
    dsimp only [F] at hh he
    rw [inner_sub_right]
    linarith
  have hdu : DifferentiableAt ℝ (fun y => u (y,z.2)) z.1 :=
    (hu.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) z.1
  have hslope := support_slope_eq_spatialGrad hdu hzball hsl
  refine ⟨z,⟨⟨hzball,hza,hzb⟩,?_⟩,?_⟩
  · intro y hy s hs
    have hh := hsupport y hy s hs
    have he := hzF
    dsimp only [F] at hh he
    rw [← hslope,inner_sub_right]
    linarith
  · apply Prod.ext
    · exact hslope.symm
    · change u z-inner ℝ z.1 (spatialGrad u z) = height
      rw [← hslope,real_inner_comm]
      exact hzF

def contactMapDerivative {n : ℕ} (u : Point n → ℝ) (z : Point n) : Point n →L[ℝ] Point n :=
  (fderiv ℝ (spatialGrad u) z).prod
    (fderiv ℝ u z-
      (innerSL ℝ (spatialGrad u z)).comp (ContinuousLinearMap.fst ℝ (Space n) ℝ)-
      (innerSL ℝ z.1).comp (fderiv ℝ (spatialGrad u) z))

theorem hasFDerivAt_contactMap {n : ℕ} {u : Point n → ℝ} (hu : ContDiff ℝ ∞ u)
    (z : Point n) : HasFDerivAt (contactMap u) (contactMapDerivative u z) z := by
  have hg := ((spatialGrad_smooth hu).differentiable (by simp) z).hasFDerivAt
  have hh := (hu.differentiable (by simp) z).hasFDerivAt.sub
    ((ContinuousLinearMap.fst ℝ (Space n) ℝ).hasFDerivAt.inner ℝ hg)
  have he : contactMapDerivative u z = (fderiv ℝ (spatialGrad u) z).prod
      (fderiv ℝ u z-
        (fderivInnerCLM ℝ (z.1,spatialGrad u z)).comp
          ((ContinuousLinearMap.fst ℝ (Space n) ℝ).prod (fderiv ℝ (spatialGrad u) z))) := by
    apply ContinuousLinearMap.ext
    intro v
    apply Prod.ext
    · rfl
    · change fderiv ℝ u z v-inner ℝ (spatialGrad u z) v.1-
          inner ℝ z.1 (fderiv ℝ (spatialGrad u) z v) =
        fderiv ℝ u z v-(inner ℝ z.1 (fderiv ℝ (spatialGrad u) z v)+inner ℝ v.1 (spatialGrad u z))
      rw [real_inner_comm v.1]
      ring
  rw [he]
  exact hg.prodMk hh

theorem contactMap_derivative_apply {n : ℕ} {u : Point n → ℝ}
    (hu : ContDiff ℝ ∞ u) (z v : Point n) :
    fderiv ℝ (contactMap u) z v =
      (fderiv ℝ (spatialGrad u) z v,
        fderiv ℝ u z v-inner ℝ (spatialGrad u z) v.1-
          inner ℝ z.1 (fderiv ℝ (spatialGrad u) z v)) := by
  rw [(hasFDerivAt_contactMap hu z).fderiv]
  rfl

end Yau.LeafProofs.L05Aux

import Yau.LeafProofs.L05ABPQuadraticAlgebra
import Yau.LeafProofs.L05ABPMaximizers

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem supRegularize_maximizer_lift_near {n : ℕ}
    {f : Point n → ℝ} {M epsilon delta : ℝ}
    (hf : Continuous f) (hM : 0≤M) (hb : ∀ q, |f q|≤M)
    (hepsilon : 0<epsilon) (hdelta : 0<delta) {y0 : Point n} {p : Space n}
    (hcenter : ∀ q, supRegularize epsilon f y0=f q-qnorm2 (y0-q)/(2*epsilon) →
      supSpatialSlope epsilon y0 q=p)
    {S : Set (Point n)} (hS : S∈𝓝 (y0.1+delta • p,y0.2)) :
    ∀ᶠ Y in 𝓝 y0, ∀ q,
      supRegularize epsilon f Y=f q-qnorm2 (Y-q)/(2*epsilon) →
        (Y.1+delta • supSpatialSlope epsilon Y q,Y.2)∈S := by
  obtain ⟨s,hs,hball⟩ := Metric.mem_nhds_iff.mp hS
  have hnear := supRegularize_maximizer_slopes_near hf hM hb hepsilon hcenter
    (show 0<s/(2*delta) by positivity)
  filter_upwards [hnear,Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (show 0<s/2 by positivity))]
    with Y hY hdist
  intro q hq
  apply hball
  rw [Metric.mem_ball,dist_eq_norm]
  have he : ((Y.1+delta • supSpatialSlope epsilon Y q,Y.2) : Point n)-
      (y0.1+delta • p,y0.2)=(Y-y0)+(delta • (supSpatialSlope epsilon Y q-p),0) := by
    apply Prod.ext
    · change Y.1+delta • supSpatialSlope epsilon Y q-(y0.1+delta • p)=
        (Y.1-y0.1)+delta • (supSpatialSlope epsilon Y q-p)
      module
    · change Y.2-y0.2=Y.2-y0.2+0
      ring
  rw [he]
  have hn := norm_add_le (Y-y0) ((delta • (supSpatialSlope epsilon Y q-p),0) : Point n)
  have hsecond : ‖((delta • (supSpatialSlope epsilon Y q-p),0) : Point n)‖=
      delta*‖supSpatialSlope epsilon Y q-p‖ := by
    simp only [Prod.norm_def,norm_zero,norm_smul,Real.norm_eq_abs,abs_of_pos hdelta]
    exact max_eq_left (mul_nonneg hdelta.le (norm_nonneg _))
  rw [hsecond] at hn
  have hy : ‖Y-y0‖<s/2 := by simpa only [dist_eq_norm] using Metric.mem_ball.mp hdist
  have hr := (lt_div_iff₀ (show 0<2*delta by positivity)).mp (hY q hq)
  linarith

theorem supRegularize_maximizer_inf_value {n : ℕ}
    {f : Point n → ℝ} {M epsilon delta : ℝ}
    (hf : Continuous f) (hM : 0≤M) (hb : ∀ q, |f q|≤M)
    (hepsilon : 0<epsilon) (hdelta : 0<delta) (hde : delta<epsilon)
    {Y q : Point n} (hq : supRegularize epsilon f Y=f q-qnorm2 (Y-q)/(2*epsilon)) :
    spatialInfRegularize delta (supRegularize epsilon f)
      (Y.1+delta • supSpatialSlope epsilon Y q,Y.2)=
      supRegularize epsilon f Y+(delta/2)*‖supSpatialSlope epsilon Y q‖^2 := by
  exact spatialInf_eq_of_lower_support (supRegularize_continuous hf hM hb hepsilon) hM
    (fun z => (supRegularize_bounds hf hM hb hepsilon z).2) hdelta hde Y.1
    (supSpatialSlope epsilon Y q) Y.2 (supRegularize_maximizer_lower_support hf hM hb hepsilon hq)

theorem quadraticLift_touchAbove {n : ℕ}
    {f : Point n → ℝ} {M epsilon delta eta c a0 : ℝ}
    (hf : Continuous f) (hM : 0≤M) (hb : ∀ q, |f q|≤M)
    (hepsilon : 0<epsilon) (hdelta : 0<delta) (hde : delta<epsilon)
    (heta : 0<eta) (hsmall : 8*delta*eta<1)
    (B : Point n →L[ℝ] Point n →L[ℝ] ℝ) (hB : ∀ v w, B v w=B w v)
    (hneg : ∀ v : Space n, 0≤-B (v,0) (v,0))
    (hlow : ∀ v : Space n, delta*(-B (v,0) (v,0))≤‖v‖^2)
    (y0 : Point n) (p : Space n)
    (hcenter : ∀ q, supRegularize epsilon f y0=f q-qnorm2 (y0-q)/(2*epsilon) →
      supSpatialSlope epsilon y0 q=p)
    (hphi : touchAbove
      (peanoPolynomial c (y0.1+delta • p,y0.2) (contactLinear p a0) B eta)
      (spatialInfRegularize delta (supRegularize epsilon f)) (y0.1+delta • p,y0.2)) :
    touchAbove (quadraticLift c y0 p a0 delta eta B) (supRegularize epsilon f) y0 := by
  let z : Point n := (y0.1+delta • p,y0.2)
  let W := spatialInfRegularize delta (supRegularize epsilon f)
  let phi := peanoPolynomial c z (contactLinear p a0) B eta
  have hc : c=W z := by simpa [peanoPolynomial,qnorm2] using hphi.1
  obtain ⟨q0,hq0,_,_⟩ := supRegularize_attained hf hM hb hepsilon y0
  have hv0 := supRegularize_maximizer_inf_value hf hM hb hepsilon hdelta hde hq0
  rw [hcenter q0 hq0] at hv0
  refine ⟨?_,?_⟩
  · rw [quadraticLift_center]
    change W z=_ at hv0
    linarith
  · have hnear := supRegularize_maximizer_lift_near hf hM hb hepsilon hdelta hcenter hphi.2
    filter_upwards [hnear] with Y hY
    obtain ⟨q,hq,_,_⟩ := supRegularize_attained hf hM hb hepsilon Y
    let r := supSpatialSlope epsilon Y q
    let X : Point n := (Y.1+delta • r,Y.2)
    have hupper : W X≤phi X := hY q hq
    have hv : W X=supRegularize epsilon f Y+(delta/2)*‖r‖^2 :=
      supRegularize_maximizer_inf_value hf hM hb hepsilon hdelta hde hq
    have hpen : ‖X.1-Y.1‖^2/(2*delta)=(delta/2)*‖r‖^2 := by
      simp only [X,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
      field_simp
    have hdom := quadratic_touch_domination hdelta heta hsmall B hB hneg hlow c a0 p
      (X.1-z.1) (Y.1-y0.1) (Y.2-y0.2)
    have hdiff : X.1-z.1-(Y.1-y0.1)+delta • p=X.1-Y.1 := by dsimp only [z]; module
    rw [hdiff] at hdom
    have hpoly : phi X-‖X.1-Y.1‖^2/(2*delta)≤quadraticLift c y0 p a0 delta eta B Y := by
      rw [quadraticLift_apply]
      simpa only [phi,peanoPolynomial,contactLinear_apply,qnorm2,Prod.fst_sub,Prod.snd_sub,
        z,X,Prod.mk_sub_mk,add_assoc] using hdom
    rw [hpen] at hpoly
    linarith

end Yau.LeafProofs.L05Aux

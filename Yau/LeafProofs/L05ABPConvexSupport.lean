import Yau.LeafProofs.L05ABPRegularization

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem strongConvex_minimum_lower {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {m : ℝ} (hf : StrongConvexOn Set.univ m f) {y : E}
    (hy : ∀ r, f y ≤ f r) (r : E) : f y+(m/2)*‖y-r‖^2 ≤ f r := by
  have hlim : Tendsto (fun s : ℝ => f r-f y-(m/2)*(1-s)*‖y-r‖^2)
      (𝓝[>] 0) (𝓝 (f r-f y-(m/2)*‖y-r‖^2)) := by
    have hc : Continuous (fun s : ℝ => f r-f y-(m/2)*(1-s)*‖y-r‖^2) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hnon : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 ≤ f r-f y-(m/2)*(1-s)*‖y-r‖^2 := by
    have hlt : ∀ᶠ s in 𝓝[>] (0:ℝ), s<1 :=
      (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,hlt] with s hs hs1
    have hs0 : 0<s := hs
    have hj := hf.2 (Set.mem_univ y) (Set.mem_univ r)
      (sub_nonneg.mpr hs1.le) hs0.le (by ring : (1-s)+s=1)
    have hmin := hy ((1-s) • y+s • r)
    change f ((1-s) • y+s • r) ≤ (1-s)*f y+s*f r-(1-s)*s*((m/2)*‖y-r‖^2) at hj
    have hm : 0 ≤ s*(f r-f y-(m/2)*(1-s)*‖y-r‖^2) := by nlinarith
    exact nonneg_of_mul_nonneg_right hm hs0
  have h0 := ge_of_tendsto hlim hnon
  linarith

theorem spatialInf_minimizer_lower_support {n : ℕ} {u : Point n → ℝ} {epsilon delta : ℝ}
    (hu : ConvexOn ℝ Set.univ (fun z => u z+qnorm2 z/(2*epsilon)))
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) (x : Space n) (t : ℝ) {y : Space n}
    (hy : ∀ r : Space n, u (y,t)+‖x-y‖^2/(2*delta) ≤ u (r,t)+‖x-r‖^2/(2*delta))
    (h : Space n) :
    u (y,t)+inner ℝ (delta⁻¹ • (x-y)) h-‖h‖^2/(2*epsilon) ≤ u (y+h,t) := by
  have hlo := strongConvex_minimum_lower (spatialInf_cost_strongConvex hu x t) hy (y+h)
  simp only [sub_add_cancel_left,norm_neg] at hlo
  rw [show x-(y+h)=(x-y)-h by abel,norm_sub_sq_real (x-y) h] at hlo
  rw [real_inner_smul_left]
  field_simp [hdelta.ne',hepsilon.ne'] at hlo ⊢
  nlinarith

theorem supRegularize_maximizer_lower_support {n : ℕ} {v : Point n → ℝ} {B epsilon : ℝ}
    (hv : Continuous v) (hB : 0 ≤ B) (hb : ∀ r, |v r| ≤ B) (hepsilon : 0 < epsilon)
    {y q : Point n} (hq : supRegularize epsilon v y=v q-qnorm2 (y-q)/(2*epsilon))
    (h : Space n) :
    supRegularize epsilon v y+inner ℝ (epsilon⁻¹ • (q.1-y.1)) h-‖h‖^2/(2*epsilon) ≤
      supRegularize epsilon v (y.1+h,y.2) := by
  have hc := le_supRegularize hv hB hb hepsilon (y.1+h,y.2) q
  have he : qnorm2 ((y.1+h,y.2)-q) = qnorm2 (y-q)+2*inner ℝ (y.1-q.1) h+‖h‖^2 := by
    dsimp only [qnorm2]
    change ‖y.1+h-q.1‖^2+(y.2-q.2)^2 =
      ‖y.1-q.1‖^2+(y.2-q.2)^2+2*inner ℝ (y.1-q.1) h+‖h‖^2
    rw [show y.1+h-q.1=(y.1-q.1)+h by abel,norm_add_sq_real]
    ring
  rw [he] at hc
  rw [hq,real_inner_smul_left,show q.1-y.1=-(y.1-q.1) by abel,inner_neg_left]
  have heq : v q-qnorm2 (y-q)/(2*epsilon)+epsilon⁻¹*(-inner ℝ (y.1-q.1) h)-
      ‖h‖^2/(2*epsilon) =
      v q-(qnorm2 (y-q)+2*inner ℝ (y.1-q.1) h+‖h‖^2)/(2*epsilon) := by
    field_simp
    ring
  rw [heq]
  exact hc

theorem spatialInf_eq_of_lower_support {n : ℕ} {u : Point n → ℝ} {B epsilon delta : ℝ}
    (hu : Continuous u) (hB : 0 ≤ B) (hb : ∀ r, |u r| ≤ B)
    (hdelta : 0 < delta) (hde : delta < epsilon) (y p : Space n) (t : ℝ)
    (hsupport : ∀ h : Space n, u (y,t)+inner ℝ p h-‖h‖^2/(2*epsilon) ≤ u (y+h,t)) :
    spatialInfRegularize delta u (y+delta • p,t)=u (y,t)+(delta/2)*‖p‖^2 := by
  have hepsilon : 0 < epsilon := hdelta.trans hde
  obtain ⟨r,hr,hmin,_⟩ := spatialInfRegularize_attained hu hB hb hdelta (y+delta • p,t)
  have hlo := hsupport (r-y)
  rw [add_sub_cancel] at hlo
  have hcost : u (y,t)+(delta/2)*‖p‖^2 ≤ u (r,t)+‖y+delta • p-r‖^2/(2*delta) := by
    rw [show y+delta • p-r=delta • p-(r-y) by abel,norm_sub_sq_real,norm_smul,
      Real.norm_eq_abs,mul_pow,sq_abs,real_inner_smul_left]
    have hcoef : 0 ≤ (delta⁻¹-epsilon⁻¹)*‖r-y‖^2 := by
      apply mul_nonneg _ (sq_nonneg _)
      have hd := one_div_lt_one_div_of_lt hdelta hde
      simpa only [one_div] using sub_nonneg.mpr hd.le
    field_simp [hdelta.ne',hepsilon.ne'] at hlo hcoef ⊢
    nlinarith
  apply le_antisymm
  · have hc := spatialInfRegularize_le_candidate hu hB hb hdelta (y+delta • p,t) y
    have he : ‖y+delta • p-y‖^2/(2*delta)=(delta/2)*‖p‖^2 := by
      rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
      field_simp
    simpa only [he] using hc
  · simpa only [hr] using hcost

theorem spatial_lower_support_convexCombination {n : ℕ} {u : Point n → ℝ}
    {epsilon : ℝ} {y p r : Space n} {t a b : ℝ}
    (hp : ∀ h : Space n, u (y,t)+inner ℝ p h-‖h‖^2/(2*epsilon) ≤ u (y+h,t))
    (hr : ∀ h : Space n, u (y,t)+inner ℝ r h-‖h‖^2/(2*epsilon) ≤ u (y+h,t))
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) (h : Space n) :
    u (y,t)+inner ℝ (a • p+b • r) h-‖h‖^2/(2*epsilon) ≤ u (y+h,t) := by
  have hp' := mul_le_mul_of_nonneg_left (hp h) ha
  have hr' := mul_le_mul_of_nonneg_left (hr h) hb
  rw [inner_add_left,real_inner_smul_left,real_inner_smul_left]
  have hm : a*u (y+h,t)+b*u (y+h,t)=u (y+h,t) := by rw [← add_mul,hab,one_mul]
  have hu : a*u (y,t)+b*u (y,t)=u (y,t) := by rw [← add_mul,hab,one_mul]
  have hpen : a*(‖h‖^2/(2*epsilon))+b*(‖h‖^2/(2*epsilon))=‖h‖^2/(2*epsilon) := by
    rw [← add_mul,hab,one_mul]
  linarith

theorem spatialInf_minimizer_slope {n : ℕ} {u : Point n → ℝ} {B delta : ℝ}
    (hu : Continuous u) (hB : 0 ≤ B) (hb : ∀ r, |u r| ≤ B) (hdelta : 0 < delta)
    {z : Point n} {y : Space n} {l : Space n →L[ℝ] ℝ}
    (hy : spatialInfRegularize delta u z=u (y,z.2)+‖z.1-y‖^2/(2*delta))
    (hd : HasFDerivAt (fun x : Space n => spatialInfRegularize delta u (x,z.2)) l z.1) :
    l=innerSL ℝ (delta⁻¹ • (z.1-y)) := by
  let Q : Space n → ℝ := fun x => u (y,z.2)+‖x-y‖^2/(2*delta)
  have hQ : HasFDerivAt Q (innerSL ℝ (delta⁻¹ • (z.1-y))) z.1 := by
    convert! ((((hasFDerivAt_id (𝕜 := ℝ) z.1).sub_const y).norm_sq).mul_const ((2*delta)⁻¹)).const_add
      (u (y,z.2)) using 1
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply,innerSL_apply_apply,real_inner_smul_left,smul_eq_mul,id_eq]
    field_simp
    ring
  have hmax : IsLocalMax (fun x : Space n => spatialInfRegularize delta u (x,z.2)-Q x) z.1 := by
    apply Filter.Eventually.of_forall
    intro x
    have hc := spatialInfRegularize_le_candidate hu hB hb hdelta (x,z.2) y
    change spatialInfRegularize delta u (x,z.2)-Q x ≤ spatialInfRegularize delta u z-Q z.1
    rw [hy]
    dsimp only [Q]
    rw [sub_self]
    change spatialInfRegularize delta u (x,z.2)-Q x ≤ 0
    exact sub_nonpos.mpr hc
  have he := hmax.hasFDerivAt_eq_zero (hd.sub hQ)
  exact sub_eq_zero.mp he

end Yau.LeafProofs.L05Aux

import Yau.LeafProofs.L05ABPQuadraticTouch
import Yau.LeafProofs.L05ABPQuadraticForms
import Yau.LeafProofs.L05ABPLocalViscosity
import Yau.LeafProofs.L05ABPAlgebra

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem pucci_half_contact_limit {n : ℕ} {ell L delta a0 G : ℝ}
    (hell : 0<ell) (hL : ell≤L) (hdelta : 0<delta) (H : Sym n)
    (hH : (-(H : Mat n)).PosSemidef)
    (htest : ∀ eta : ℝ, 0<eta → 8*delta*eta<1 →
      a0-pucciPlus ell L (((1-8*delta*eta)/2) • H+(8*eta) • sym (1 : Mat n))≤G) :
    a0+(ell/2)*Matrix.trace (-(H : Mat n))≤G := by
  have hc : Continuous (fun eta : ℝ =>
      a0-pucciPlus ell L (((1-8*delta*eta)/2) • H+(8*eta) • sym (1 : Mat n))) := by
    apply continuous_const.sub
    apply (pucciPlus_continuous hell.le hL).comp
    apply continuous_induced_rng.mpr
    change Continuous (fun eta : ℝ =>
      ((1-8*delta*eta)/2) • (H : Mat n)+(8*eta) • (sym (1 : Mat n) : Mat n))
    fun_prop
  have ht : Tendsto (fun eta : ℝ =>
      a0-pucciPlus ell L (((1-8*delta*eta)/2) • H+(8*eta) • sym (1 : Mat n)))
      (𝓝[>] 0) (𝓝 (a0-pucciPlus ell L ((1/2 : ℝ) • H))) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ eta in 𝓝[>] (0:ℝ), eta<1/(8*delta) :=
    (eventually_lt_nhds (by positivity : (0:ℝ)<1/(8*delta))).filter_mono nhdsWithin_le_nhds
  have hh : a0-pucciPlus ell L ((1/2 : ℝ) • H)≤G := by
    apply le_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin,hsmall] with eta heta hsmall
    apply htest eta heta
    have hs := (lt_div_iff₀ (by positivity : 0<8*delta)).mp hsmall
    nlinarith
  have hhalf : (-(((1/2 : ℝ) • H : Sym n) : Mat n)).PosSemidef := by
    change (-((1/2 : ℝ) • (H : Mat n))).PosSemidef
    rw [←smul_neg]
    exact hH.smul (by norm_num)
  rw [pucciPlus_of_nonpos hell.le hL ((1/2 : ℝ) • H) hhalf] at hh
  change a0-ell*Matrix.trace ((1/2 : ℝ) • (H : Mat n))≤G at hh
  rw [Matrix.trace_smul,smul_eq_mul] at hh
  rw [Matrix.trace_neg]
  linarith

theorem lasryLions_peano_contact_inequality {n : ℕ}
    {f v g : Point n → ℝ} {M epsilon ell L R a b : ℝ} {Q : Set (Point n)}
    (hf : Continuous f) (hM : 0≤M) (hb : ∀ q, |f q|≤M)
    (hepsilon : 0<epsilon) (hell : 0<ell) (hL : ell≤L)
    (hQ : IsOpen Q) (heq : Set.EqOn f v Q)
    (hsub : viscositySub Q (fun H _ => pucciPlus ell L H) g v)
    {z : Point n} {xi : Space n} {l : Point n →L[ℝ] ℝ}
    {B : Point n →L[ℝ] Point n →L[ℝ] ℝ}
    (hz : z∈abpOpen n R a b)
    (hs : pastSupports R a
      (spatialInfRegularize (epsilon/2) (supRegularize epsilon f)) z xi)
    (hjet : jointPeanoJet
      (spatialInfRegularize (epsilon/2) (supRegularize epsilon f)) z l B)
    {y : Space n}
    (hy : spatialInfRegularize (epsilon/2) (supRegularize epsilon f) z=
      supRegularize epsilon f (y,z.2)+‖z.1-y‖^2/(2*(epsilon/2)))
    {q0 : Point n} (hqQ : q0∈Q)
    (hq : supRegularize epsilon f (y,z.2)=f q0-qnorm2 ((y,z.2)-q0)/(2*epsilon)) :
    l (0,1)+(ell/2)*Matrix.trace (-(jointHessian B : Mat n))≤g q0 := by
  let delta := epsilon/2
  let U := supRegularize epsilon f
  let W := spatialInfRegularize delta U
  let p := delta⁻¹ • (z.1-y)
  let y0 : Point n := (y,z.2)
  have hd : 0<delta := by dsimp [delta]; positivity
  have hde : delta<epsilon := by dsimp [delta]; linarith
  have hU : Continuous U := supRegularize_continuous hf hM hb hepsilon
  have hbU : ∀ q, |U q|≤M := fun q => (supRegularize_bounds hf hM hb hepsilon q).2
  have hzcenter : ((y0.1+delta • p,y0.2) : Point n)=z := by
    apply Prod.ext
    · dsimp only [y0,p]
      rw [smul_smul,mul_inv_cancel₀ hd.ne',one_smul]
      abel
    · rfl
  have hfd : HasFDerivAt W l z := jointPeanoJet_hasFDerivAt hjet
  have hinc : HasFDerivAt (fun x : Space n => (x,z.2))
      (ContinuousLinearMap.inl ℝ (Space n) ℝ) z.1 := by
    simpa only [ContinuousLinearMap.inl_apply,Prod.mk_add_mk,zero_add,add_zero] using
      ((ContinuousLinearMap.inl ℝ (Space n) ℝ).hasFDerivAt (x := z.1)).add_const ((0,z.2) : Point n)
  have hsp : HasFDerivAt (fun x : Space n => W (x,z.2))
      (l.comp (ContinuousLinearMap.inl ℝ (Space n) ℝ)) z.1 := by
    convert! hfd.comp z.1 hinc using 1
  have hlp : l.comp (ContinuousLinearMap.inl ℝ (Space n) ℝ)=innerSL ℝ p :=
    spatialInf_minimizer_slope hU hM hbU hd hy hsp
  have hgrad : spatialGrad W z=p := by
    apply ext_inner_right ℝ
    intro r
    rw [spatialGrad_inner,jointPeanoJet_spatialD hjet,hlp]
    rfl
  have hxi : xi=p := by
    rw [←hgrad]
    exact support_slope_eq_spatialGrad hsp.differentiableAt hz.1
      (fun x hx => hs x hx z.2 ⟨hz.2.1.le,le_rfl⟩)
  have hl : l=contactLinear p (l (0,1)) := by
    apply ContinuousLinearMap.ext
    intro r
    have hr : r=(r.1,0)+r.2 • ((0,1) : Point n) := by ext <;> simp
    have hspace := congrArg (fun A : Space n →L[ℝ] ℝ => A r.1) hlp
    change l (r.1,0)=inner ℝ p r.1 at hspace
    rw [contactLinear_apply]
    conv_lhs => rw [hr,map_add,map_smul]
    rw [hspace]
    simp only [smul_eq_mul]
    ring
  have hpLower : ∀ h : Space n, U y0+inner ℝ p h-‖h‖^2/(2*epsilon)≤U (y+h,z.2) := by
    apply spatialInf_minimizer_lower_support (supRegularize_semiconvex hf hM hb hepsilon)
      hd hepsilon z.1 z.2
    intro r
    rw [←hy]
    exact spatialInfRegularize_le_candidate hU hM hbU hd z r
  have hcenter : ∀ q, U y0=f q-qnorm2 (y0-q)/(2*epsilon) →
      supSpatialSlope epsilon y0 q=p := by
    intro q hq
    have hqLower := supRegularize_maximizer_lower_support hf hM hb hepsilon hq
    apply spatialInf_contact_slope_unique hU hM hbU hd hde hpLower hqLower
    · simpa only [←hzcenter] using hz.1
    · intro x hx
      have hh := hs x hx z.2 ⟨hz.2.1.le,le_rfl⟩
      rw [hxi] at hh
      simpa only [←hzcenter] using hh
  have hsemi := (lasryLions_semiconvex_semiconcave hf hM hb hepsilon).1
  have hW : Continuous W := (jointSemiconvex_locallyLipschitz hsemi).continuous
  have hneg := jointPeanoJet_pastSupport_hessian_nonpos hz hs hjet
  have hlow := jointPeanoJet_semiconvex_hessian_lower hW hsemi hjet
  have hcoef : 2/epsilon=delta⁻¹ := by dsimp [delta]; field_simp
  rw [hcoef] at hlow
  obtain ⟨hnegForm,hlowForm⟩ := jointHessian_spatial_form_bounds hd B hjet.1 hneg hlow
  apply pucci_half_contact_limit hell hL hd (jointHessian B) hneg
  intro eta heta hsmall
  have hphi := jointPeanoJet_upper_test hjet heta
  rw [hl] at hphi
  rw [←hzcenter] at hphi
  have htouch := quadraticLift_touchAbove hf hM hb hepsilon hd hde heta hsmall B hjet.1
    hnegForm hlowForm y0 p hcenter hphi
  have htouch' : touchAbove (quadraticLift (W z) y0 p (l (0,1)) delta eta B) U y0 := by
    simpa only [hzcenter] using htouch
  have hv := supRegularize_local_viscosity_jet hf hM hb hepsilon hQ heq hsub hqQ hq
    ((quadraticLift_smooth (W z) y0 p (l (0,1)) delta eta B).contDiffAt.of_le (by simp)) htouch'
  rw [quadraticLift_timeD _ _ _ _ _ _ _ hjet.1,quadraticLift_hessian _ _ _ _ _ _ _ hjet.1] at hv
  exact hv

end Yau.LeafProofs.L05Aux

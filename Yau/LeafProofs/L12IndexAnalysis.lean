import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! General analytic facts used in the index-form argument. -/

open Filter Asymptotics
open scoped Topology

namespace Yau.LeafProofs.L12Aux

/-- A continuous coefficient suffices in the product rule when the differentiable factor
vanishes at the point of differentiation. -/
theorem hasFDerivAt_clm_apply_of_zero
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {L : E → F →L[ℝ] G} {m : E → F} {z : E} {m' : E →L[ℝ] F}
    (hL : ContinuousAt L z) (hm : HasFDerivAt m m' z) (hm0 : m z = 0) :
    HasFDerivAt (fun x => L x (m x)) ((L z).comp m') z := by
  have hprod : (fun x => ‖L x - L z‖ * ‖m x‖) =o[𝓝 z]
      (fun x => ‖x - z‖) := by
    simpa only [hm0, sub_zero, one_mul] using
      (hL.isLittleO (F := ℝ)).norm_left.mul_isBigO hm.isBigO_sub.norm_left.norm_right
  have hrem : (fun x => (L x - L z) (m x)) =o[𝓝 z] (fun x => x - z) := by
    exact isLittleO_norm_right.mp <|
      isBoundedBilinearMap_apply.isBigO_comp.trans_isLittleO hprod
  have hfixed : HasFDerivAt (fun x => L z (m x)) ((L z).comp m') z :=
    (L z).hasFDerivAt.comp z hm
  apply HasFDerivAt.of_isLittleO
  convert hrem.add hfixed.isLittleO using 1
  ext x
  simp only [sub_apply, hm0, map_zero, sub_zero]
  abel

/-- The Hessian of a real function at a local minimum has nonnegative diagonal.
Only the actual derivative field near the point and its derivative at the point are used. -/
theorem localMin_hessian_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {H : E →L[ℝ] E →L[ℝ] ℝ} {z : E}
    (hmin : IsLocalMin f z)
    (hfirst : ∀ᶠ x in 𝓝 z, HasFDerivAt f (f' x) x)
    (hsecond : HasFDerivAt f' H z) (a : E) : 0 ≤ H a a := by
  let γ : ℝ → E := fun t => z + t • a
  let g : ℝ → ℝ := fun t => f (γ t)
  let g' : ℝ → ℝ := fun t => f' (γ t) a
  have hγ (t : ℝ) : HasDerivAt γ a t := by
    simpa [γ] using ((hasDerivAt_id t).smul_const a).const_add z
  have hγ0 : γ 0 = z := by simp [γ]
  have hfirstline : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt g (g' t) t := by
    filter_upwards [(hγ 0).continuousAt.tendsto.eventually (hγ0 ▸ hfirst)] with t ht
    exact ht.comp_hasDerivAt t (hγ t)
  have hsecondline : HasDerivAt g' (H a a) 0 := by
    have hfield : HasDerivAt (fun t => f' (γ t)) (H a) 0 :=
      (hγ0 ▸ hsecond).comp_hasDerivAt 0 (hγ 0)
    exact (ContinuousLinearMap.apply ℝ ℝ a).hasFDerivAt.comp_hasDerivAt 0 hfield
  have hgmin : IsLocalMin g 0 :=
    (hγ0 ▸ hmin).comp_continuous (hγ 0).continuousAt
  have hderiv : deriv g =ᶠ[𝓝 (0 : ℝ)] g' :=
    hfirstline.mono fun _ ht => ht.deriv
  have hd2 : deriv (deriv g) 0 = H a a := by
    rw [hderiv.deriv_eq, hsecondline.deriv]
  by_contra hneg
  have hgmax : IsLocalMax g 0 :=
    isLocalMax_of_deriv_deriv_neg (hd2 ▸ lt_of_not_ge hneg)
      hgmin.deriv_eq_zero (hfirstline.self_of_nhds.continuousAt)
  have hconst : g =ᶠ[𝓝 (0 : ℝ)] (fun _ => g 0) := by
    filter_upwards [hgmin, hgmax] with t htmin htmax
    exact le_antisymm htmax htmin
  have hd2zero : deriv (deriv g) 0 = 0 := by
    simpa only [deriv_const', deriv_const] using hconst.deriv.deriv_eq
  exact (lt_of_not_ge hneg).ne (hd2.symm.trans hd2zero)

/-- At a local minimum, a null diagonal direction of the genuine Hessian annihilates
all mixed terms. This holds on any real normed space. -/
theorem localMin_hessian_null
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {H : E →L[ℝ] E →L[ℝ] ℝ} {z : E}
    (hmin : IsLocalMin f z)
    (hfirst : ∀ᶠ x in 𝓝 z, HasFDerivAt f (f' x) x)
    (hsecond : HasFDerivAt f' H z)
    {v : E} (hv : H v v = 0) : ∀ w, H v w = 0 := by
  intro w
  have hsym : H w v = H v w :=
    second_derivative_symmetric_of_eventually_of_real hfirst hsecond w v
  have hb := localMin_hessian_nonneg hmin hfirst hsecond w
  have hpos := localMin_hessian_nonneg hmin hfirst hsecond
    ((H w w + 1) • v - (H v w) • w)
  simp only [map_sub, map_smul, sub_apply,
    smul_apply, smul_eq_mul, hv, hsym] at hpos
  have hsq : (H v w) ^ 2 = 0 := by nlinarith [sq_nonneg (H v w)]
  exact sq_eq_zero_iff.mp hsq

end Yau.LeafProofs.L12Aux

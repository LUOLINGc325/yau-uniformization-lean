import Yau.LeafProofs.L05AutonomousBallMeanIBP
import Mathlib.Analysis.InnerProductSpace.Calculus

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

theorem auto_ballMean_norm_hasFDerivAt {n : ℕ} {x : Space n} (hx : x ≠ 0) :
    HasFDerivAt (fun y : Space n => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  have hF : (fun y : Space n => Real.sqrt (‖y‖^2))=(fun y => ‖y‖) := by
    funext y
    exact Real.sqrt_sq (norm_nonneg y)
  rw [hF,Real.sqrt_sq (norm_nonneg x)] at h
  convert! h using 1
  ext e
  simp only [smul_apply,smul_eq_mul,two_smul,add_apply]
  field_simp
  ; ring

theorem auto_ballMean_radial_fderiv {n : ℕ} {phi : ℝ → ℝ} {x : Space n} {v : ℝ}
    (hx : x ≠ 0) (hphi : HasDerivAt phi v ‖x‖) (e : Space n) :
    fderiv ℝ (fun y : Space n => phi ‖y‖) x e=(v/‖x‖)*inner ℝ e x := by
  have h := hphi.comp_hasFDerivAt x (auto_ballMean_norm_hasFDerivAt hx)
  change (fderiv ℝ (phi ∘ norm) x) e=_
  rw [h.fderiv]
  simp only [smul_apply,smul_eq_mul,innerSL_apply_apply,real_inner_comm x e,div_eq_mul_inv]
  ring


theorem auto_ballMean_radial_second {n : ℕ} {phi D1 D2 : ℝ → ℝ}
    (hphi : ∀ s : ℝ, 0 < s → HasDerivAt phi (D1 s) s)
    (hD1 : ∀ s : ℝ, 0 < s → HasDerivAt D1 (D2 s) s)
    (hC2 : ∀ s : ℝ, 0 < s → ContDiffAt ℝ 2 phi s)
    {x : Space n} (hx : x ≠ 0) (e : Space n) :
    (fderiv ℝ (fderiv ℝ (fun y : Space n => phi ‖y‖)) x) e e=
      (D2 ‖x‖/‖x‖^2-D1 ‖x‖/‖x‖^3)*(inner ℝ e x)^2+(D1 ‖x‖/‖x‖)*‖e‖^2 := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let C : ℝ → ℝ := fun s => D1 s/s
  have hC : HasDerivAt C ((D2 ‖x‖*‖x‖-D1 ‖x‖)/‖x‖^2) ‖x‖ := by
    convert! (hD1 ‖x‖ hn).div (hasDerivAt_id ‖x‖) hn.ne' using 1; simp [id_eq,mul_one]
  have hExpr := (hC.comp_hasFDerivAt x (auto_ballMean_norm_hasFDerivAt hx)).mul
    ((innerSL ℝ e).hasFDerivAt (x := x))
  change HasFDerivAt (fun y : Space n => C ‖y‖*inner ℝ e y) _ x at hExpr
  have hEq : (fun y : Space n => fderiv ℝ (fun z : Space n => phi ‖z‖) y e)=ᶠ[𝓝 x]
      (fun y : Space n => C ‖y‖*inner ℝ e y) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    exact auto_ballMean_radial_fderiv hy (hphi ‖y‖ (norm_pos_iff.mpr hy)) e
  have hEval := congrArg (fun L : Space n →L[ℝ] ℝ => L e) hEq.fderiv_eq
  have hW : ContDiffAt ℝ 2 (fun y : Space n => phi ‖y‖) x :=
    (hC2 ‖x‖ hn).comp x (contDiffAt_norm ℝ hx)
  rw [auto_ballMean_direction_second hW e,hExpr.fderiv] at hEval
  rw [hEval]
  dsimp only [C,Function.comp_def]
  simp only [smul_apply,add_apply,smul_eq_mul,
    innerSL_apply_apply,real_inner_self_eq_norm_sq,real_inner_comm x e]
  field_simp [hn.ne']
  ; ring

theorem auto_ballMean_radial_laplacian {n : ℕ} {phi D1 D2 : ℝ → ℝ}
    (hphi : ∀ s : ℝ, 0 < s → HasDerivAt phi (D1 s) s)
    (hD1 : ∀ s : ℝ, 0 < s → HasDerivAt D1 (D2 s) s)
    (hC2 : ∀ s : ℝ, 0 < s → ContDiffAt ℝ 2 phi s)
    {x : Space n} (hx : x ≠ 0) :
    autoBallMeanLaplacian (fun y : Space n => phi ‖y‖) x=
      D2 ‖x‖+((2*n : ℝ)-1)/‖x‖*D1 ‖x‖ := by
  have hBasis (i : Yau.RIdx n) : ‖Yau.realVec i‖=1 := by
    simpa only [complexVector_realOrthonormalBasis_apply] using
      (complexVector_realOrthonormalBasis n).orthonormal.norm_eq_one i
  have hCoord : (∑ i : Yau.RIdx n, (inner ℝ (Yau.realVec i) x)^2)=‖x‖^2 := by
    have h := (complexVector_realOrthonormalBasis n).sum_inner_mul_inner x x
    simpa only [complexVector_realOrthonormalBasis_apply,real_inner_self_eq_norm_sq,pow_two,real_inner_comm x] using h
  unfold autoBallMeanLaplacian
  simp_rw [auto_ballMean_radial_second hphi hD1 hC2 hx,hBasis,one_pow,mul_one]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,hCoord,Finset.sum_const,Finset.card_univ]
  simp only [Yau.RIdx,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp [hn]
  ; ring


theorem auto_ballMean_normSq_laplacian {n : ℕ} {x : Space n} (hx : x ≠ 0) :
    autoBallMeanLaplacian (fun y : Space n => ‖y‖^2) x=2*(2*n : ℝ) := by
  have hPhi (s : ℝ) (_hs : 0 < s) : HasDerivAt (fun t : ℝ => t^2) (2*s) s := by
    convert! (hasDerivAt_id s).pow 2 using 1; simp
  have hD1 (s : ℝ) (_hs : 0 < s) : HasDerivAt (fun t : ℝ => 2*t) 2 s := by
    convert! (hasDerivAt_id s).const_mul 2 using 1; simp
  have hC2 (s : ℝ) (_hs : 0 < s) : ContDiffAt ℝ 2 (fun t : ℝ => t^2) s := by fun_prop
  rw [auto_ballMean_radial_laplacian hPhi hD1 hC2 hx]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp [hn]
  ; ring

end Yau.LeafProofs.L05AutonomousAux

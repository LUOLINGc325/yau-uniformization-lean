import Yau.LeafProofs.L05ChuSharpRadius

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

theorem chuTransformNormConstant_nonneg (n : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ chuTransformNormConstant n K := by unfold chuTransformNormConstant; positivity

def chuAnchorDelta (n : ℕ) (K M eta beta r : ℝ) : ℝ :=
  2*chuTransformNormConstant n K*M*r^eta+2*K*(1+2*M)*r^beta

theorem chuAnchorDelta_nonneg (n : ℕ) {K M eta beta r : ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hr : 0 ≤ r) : 0 ≤ chuAnchorDelta n K M eta beta r := by
  have hC := chuTransformNormConstant_nonneg n hK
  unfold chuAnchorDelta
  positivity

theorem chu_transformed_anchor_distance {n : ℕ} {T : Sym n → Point n → Sym n}
    {S : Point n → Sym n} {K beta eta M r : ℝ} (hK : 0 ≤ K)
    (hb : 0 ≤ beta) (he : 0 ≤ eta) (hT : ChuH2 T K beta) (hS : ChuH3 S K beta)
    {Q : Set (Point n)} (hQ : Q ⊆ backward 1) {u : Point n → ℝ}
    (hH : HolderBound eta Q (hessian u) M) {p p0 : Point n}
    (hp : p ∈ Q) (hp0 : p0 ∈ Q) (hpr : parabolicDistance p p0 ≤ r) :
    ‖S p+T (hessian u p) p-(S p0+T (hessian u p0) p0)‖ ≤ chuAnchorDelta n K M eta beta r := by
  have hn := chu_transformed_difference_norm hK hT hS (hessian u p) (hessian u p0) (hQ hp) (hQ hp0)
  have hC := chuTransformNormConstant_nonneg n hK
  have hwh := holderWeight_le_twice_radius_power he hpr
  have hwt := holderWeight_le_twice_radius_power hb hpr
  have hh := (hH.2.2 p hp p0 hp0).trans (mul_le_mul_of_nonneg_left hwh hH.1)
  have hc := mul_le_mul_of_nonneg_left hh hC
  have hcoeff : K*(1+2*‖hessian u p0‖) ≤ K*(1+2*M) := by
    exact mul_le_mul_of_nonneg_left (by linarith only [hH.2.1 p0 hp0]) hK
  have hW : 0 ≤ holderWeight beta p p0 := add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)
  have hterm := mul_le_mul hcoeff hwt hW (mul_nonneg hK (by linarith only [hH.1]))
  unfold chuAnchorDelta
  nlinarith only [hn,hc,hterm]

def chuResidualSourceConstant (n : ℕ) (L K fB M wB : ℝ) : ℝ :=
  fB+K+(wB+bellmanMatrixConstant n L)*K*(1+2*M)

set_option maxHeartbeats 1600000 in
theorem chuFrozenResidual_near_bound {n : ℕ} {E U : Set (Sym n)} (hE : Convex ℝ E)
    {F : Sym n → Point n → ℝ} {T : Sym n → Point n → Sym n} {S : Point n → Sym n}
    {ell L K alpha beta fB gamma M wB epsilon : ℝ}
    (hell : 0 ≤ ell) (hL : ell ≤ L) (hK : 0 ≤ K) (hg : 0 ≤ gamma)
    (hga : gamma ≤ alpha) (hgb : gamma ≤ beta)
    (hF : ChuH1 E U F ell L K beta) (hT : ChuH2 T K beta) (hS : ChuH3 S K beta)
    {omega : ℝ → ℝ} (hm : Modulus omega) (hDF : ChuDerivativeModulus E F omega)
    {A0 : Sym n} (hA0 : A0 ∈ E) {p0 : Point n} (hp0 : p0 ∈ backward 1)
    {f u : Point n → ℝ} (hf : HolderBound alpha (backward 1) f fB)
    (hRange : ∀ p ∈ backward 1, S p+T (hessian u p) p ∈ E)
    (hPDE : ∀ p ∈ backward 1, timeD (backward 1) u p-F (S p+T (hessian u p) p) p=f p)
    {p q : Point n} (hp : p ∈ backward 1) (hq : q ∈ backward 1)
    {delta : ℝ} (hd : 0 ≤ delta) (hAd : ‖S p+T (hessian u p) p-A0‖ ≤ delta)
    (hBd : ‖S q+T (hessian u q) q-A0‖ ≤ delta) (hpq : parabolicDistance p q ≤ 1)
    (hJ : ‖hessian u q‖ ≤ M) (hwB : omega (delta+parabolicDistance p p0) ≤ wB)
    (hsmall : omega (delta+parabolicDistance p p0)*chuTransformNormConstant n K+
      2*bellmanMatrixConstant n L*K*holderWeight beta p p0 ≤ epsilon) :
    |chuFrozenResidual hT F A0 p0 hp0 u p-chuFrozenResidual hT F A0 p0 hp0 u q| ≤
      epsilon*‖hessian u p-hessian u q‖+chuResidualSourceConstant n L K fB M wB*holderWeight gamma p q := by
  have hn := chuFrozenResidual_difference hE hell hL hK hF hT hS hm hDF hA0 hp0 hf hRange hPDE hp hq hd hAd hBd
  have hwa := holderWeight_lower_exponent_near hg hga hpq
  have hwb := holderWeight_lower_exponent_near hg hgb hpq
  have hw : 0 ≤ omega (delta+parabolicDistance p p0) :=
    hm.2.1 _ (add_nonneg hd (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)))
  have hC := bellmanMatrixConstant_nonneg n (hell.trans hL)
  have hcoef : K+(omega (delta+parabolicDistance p p0)+bellmanMatrixConstant n L)*K*(1+2*‖hessian u q‖) ≤
      K+(wB+bellmanMatrixConstant n L)*K*(1+2*M) := by
    have h1 : (omega (delta+parabolicDistance p p0)+bellmanMatrixConstant n L)*K ≤
        (wB+bellmanMatrixConstant n L)*K :=
      mul_le_mul_of_nonneg_right (add_le_add hwB le_rfl) hK
    have h2 := mul_le_mul h1 (show 1+2*‖hessian u q‖ ≤ 1+2*M by linarith only [hJ])
      (by positivity : 0 ≤ 1+2*‖hessian u q‖) (mul_nonneg (add_nonneg (hw.trans hwB) hC) hK)
    exact add_le_add le_rfl h2
  have hcoef0 : 0 ≤ K+(omega (delta+parabolicDistance p p0)+bellmanMatrixConstant n L)*K*(1+2*‖hessian u q‖) := by positivity
  have ha := mul_le_mul_of_nonneg_left hwa hf.1
  have hb := mul_le_mul hcoef hwb
    (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _))
    (hcoef0.trans hcoef)
  have hs := mul_le_mul_of_nonneg_right hsmall (norm_nonneg (hessian u p-hessian u q))
  unfold chuResidualSourceConstant
  nlinarith only [hn,ha,hb,hs]

end Yau.LeafProofs.L05Aux

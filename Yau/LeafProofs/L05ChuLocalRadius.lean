import Yau.LeafProofs.L05ChuLocalResidual

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

def chuAnchorModulusBound (n : ℕ) (K M : ℝ) (omega : ℝ → ℝ) : ℝ :=
  omega (2*chuTransformNormConstant n K*M+2*K*(1+2*M)+1)

set_option maxHeartbeats 1600000 in
theorem chu_local_absorption_radius {n : ℕ} {omega : ℝ → ℝ} (hm : Modulus omega)
    {K L M eta beta epsilon : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (he : 0 < eta) (hb : 0 < beta) (heps : 0 < epsilon) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ 1 ∧ ∀ r : ℝ, 0 ≤ r → r ≤ rho →
      ∀ p p0 : Point n, parabolicDistance p p0 ≤ r →
      (omega (chuAnchorDelta n K M eta beta r+parabolicDistance p p0)*chuTransformNormConstant n K+
        2*bellmanMatrixConstant n L*K*holderWeight beta p p0 ≤ epsilon) ∧
      omega (chuAnchorDelta n K M eta beta r+parabolicDistance p p0) ≤ chuAnchorModulusBound n K M omega := by
  have hCT := chuTransformNormConstant_nonneg n hK
  have hCL := bellmanMatrixConstant_nonneg n hL
  have hA : 0 ≤ 2*chuTransformNormConstant n K*M := by positivity
  have hB : 0 ≤ 2*K*(1+2*M) := by positivity
  obtain ⟨rho,hrho,hrho1,hsmall⟩ := chu_modulus_absorption_radius hm he hb hA hB heps
    (C := chuTransformNormConstant n K) (D := 4*bellmanMatrixConstant n L*K)
  refine ⟨rho,hrho,hrho1,?_⟩
  intro r hr hrle p p0 hpr
  have hr1 := hrle.trans hrho1
  have hd := chuAnchorDelta_nonneg n hK hM hr (eta := eta) (beta := beta)
  have hpdist : 0 ≤ parabolicDistance p p0 := add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hmono := hm.2.2.1 (show chuAnchorDelta n K M eta beta r+parabolicDistance p p0 ∈ Set.Ici 0 from add_nonneg hd hpdist)
    (show chuAnchorDelta n K M eta beta r+r ∈ Set.Ici 0 from add_nonneg hd hr) (add_le_add le_rfl hpr)
  have hw := holderWeight_le_twice_radius_power hb.le hpr
  have hcoef := mul_le_mul_of_nonneg_left hmono hCT
  have htime := mul_le_mul_of_nonneg_left hw
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hCL) hK)
  have hs := hsmall r hr hrle
  change chuTransformNormConstant n K*omega (chuAnchorDelta n K M eta beta r+r)+
    4*bellmanMatrixConstant n L*K*r^beta ≤ epsilon at hs
  have hc := mul_le_mul_of_nonneg_left (Real.rpow_le_one hr hr1 he.le) hA
  have ht := mul_le_mul_of_nonneg_left (Real.rpow_le_one hr hr1 hb.le) hB
  have hcap : chuAnchorDelta n K M eta beta r+parabolicDistance p p0 ≤
      2*chuTransformNormConstant n K*M+2*K*(1+2*M)+1 := by
    unfold chuAnchorDelta
    nlinarith only [hc,ht,hpr,hr1]
  constructor
  · nlinarith only [hcoef,htime,hs]
  · exact hm.2.2.1 (add_nonneg hd hpdist)
      (show 0 ≤ 2*chuTransformNormConstant n K*M+2*K*(1+2*M)+1 from by positivity) hcap

set_option maxHeartbeats 1800000 in
theorem chu_local_residual_bound {n : ℕ} {omega : ℝ → ℝ} (hm : Modulus omega)
    {ell L K M eta alpha beta fB gamma epsilon : ℝ}
    (hell : 0 ≤ ell) (hL : ell ≤ L) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (he : 0 < eta) (hb : 0 < beta) (hg : 0 ≤ gamma) (hga : gamma ≤ alpha)
    (hgb : gamma ≤ beta) (heps : 0 < epsilon) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ 1 ∧
      ∀ (E U : Set (Sym n)) (F : Sym n → Point n → ℝ) (T : Sym n → Point n → Sym n)
        (S : Point n → Sym n) (f u : Point n → ℝ) (Q : Set (Point n)),
      Convex ℝ E → ∀ (hF : ChuH1 E U F ell L K beta) (hT : ChuH2 T K beta),
      ChuH3 S K beta → ChuDerivativeModulus E F omega → HolderBound alpha (backward 1) f fB →
      ∀ hQ : Q ⊆ backward 1, HolderBound eta Q (hessian u) M →
      (∀ p ∈ backward 1, S p+T (hessian u p) p ∈ E) →
      (∀ p ∈ backward 1, timeD (backward 1) u p-F (S p+T (hessian u p) p) p=f p) →
      ∀ p0 : Point n, ∀ hp0 : p0 ∈ Q, ∀ p ∈ Q, ∀ q ∈ Q,
      parabolicDistance p p0 ≤ rho → parabolicDistance q p0 ≤ rho → parabolicDistance p q ≤ 1 →
      |chuFrozenResidual hT F (S p0+T (hessian u p0) p0) p0 (hQ hp0) u p-
        chuFrozenResidual hT F (S p0+T (hessian u p0) p0) p0 (hQ hp0) u q| ≤
        epsilon*‖hessian u p-hessian u q‖+
          chuResidualSourceConstant n L K fB M (chuAnchorModulusBound n K M omega)*holderWeight gamma p q := by
  obtain ⟨rho,hrho,hrho1,hrule⟩ := chu_local_absorption_radius hm hK (hell.trans hL) hM he hb heps
  refine ⟨rho,hrho,hrho1,?_⟩
  intro E U F T S f u Q hE hF hT hS hDF hf hQ hH hRange hPDE p0 hp0 p hp q hq hpr hqr hpq
  have ha := chu_transformed_anchor_distance hK hb.le he.le hT hS hQ hH hp hp0 hpr
  have hqA := chu_transformed_anchor_distance hK hb.le he.le hT hS hQ hH hq hp0 hqr
  have hd := chuAnchorDelta_nonneg n hK hM hrho.le (eta := eta) (beta := beta)
  have hsmall := hrule rho hrho.le le_rfl p p0 hpr
  exact chuFrozenResidual_near_bound hE hell hL hK hg hga hgb hF hT hS hm hDF
    (hRange p0 (hQ hp0)) (hQ hp0) hf hRange hPDE (hQ hp) (hQ hq) hd ha hqA hpq
    (hH.2.1 q hq) hsmall.2 hsmall.1

end Yau.LeafProofs.L05Aux

import Yau.Proofs.C05HessianPropagationSegment

/-! A third scalar-jet bound propagates center Hessian negativity on the
same actual intrinsic ball, with the literal metric normalization 2 Re h. -/
noncomputable section
open scoped Topology ContDiff Manifold
namespace Yau.Proofs.C05HessianPropagationAux
open Yau Yau.Proofs.C05Aux Yau.Proofs.C05GradientFlowAux
variable {n : ℕ} {M : ComplexManifold n}

 theorem realHess_le_of_center (g : SmoothMetric M) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) (o : M.Carrier) {C R b : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hthird : ∀ x ∈ distBall g.form o R, scalarJetNorm g.form f 3 x ≤ C)
    (hcenter : ∀ w : TangentVector M o, realHess g.form f o w w ≤ -b*realNormSq g.form o w)
    (x : M.Carrier) (hx : x ∈ distBall g.form o R) (v : TangentVector M x) :
    realHess g.form f x v v ≤
      (-b+C*inducedDistance g.form o x)*realNormSq g.form x v := by
  obtain ⟨w,hwN,hwH⟩ := exists_center_vector_hessian_difference_le g f hf o hC hR hthird x hx v
  have hc := hcenter w
  rw [hwN] at hc
  have hd := (le_abs_self (realHess g.form f x v v-realHess g.form f o w w)).trans hwH
  nlinarith

 theorem realHess_le_neg_on_ball (g : SmoothMetric M) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) (o : M.Carrier) {C R a : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hthird : ∀ x ∈ distBall g.form o R, scalarJetNorm g.form f 3 x ≤ C)
    (hcenter : ∀ w : TangentVector M o, realHess g.form f o w w ≤ -(2*a)*realNormSq g.form o w)
    (hradius : C*R ≤ a) (x : M.Carrier) (hx : x ∈ distBall g.form o R)
    (v : TangentVector M x) :
    realHess g.form f x v v ≤ -a*realNormSq g.form x v := by
  have H := realHess_le_of_center g f hf o hC hR hthird hcenter x hx v
  have hdist := (Yau.LeafProofs.L12Aux.mem_distBall_iff g o x hR).mp hx
  have hcoef : -(2*a)+C*inducedDistance g.form o x ≤ -a := by
    have hc := (mul_le_mul_of_nonneg_left hdist.le hC).trans hradius
    linarith
  exact H.trans (mul_le_mul_of_nonneg_right hcoef (realNormSq_nonneg g.form x v))

 theorem realHess_le_neg_of_radius_le_div (g : SmoothMetric M) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) (o : M.Carrier) {C R a : ℝ} (hC : 0 < C) (hR : 0 < R)
    (hthird : ∀ x ∈ distBall g.form o R, scalarJetNorm g.form f 3 x ≤ C)
    (hcenter : ∀ w : TangentVector M o, realHess g.form f o w w ≤ -(2*a)*realNormSq g.form o w)
    (hradius : R ≤ a/C) (x : M.Carrier) (hx : x ∈ distBall g.form o R)
    (v : TangentVector M x) :
    realHess g.form f x v v ≤ -a*realNormSq g.form x v := by
  apply realHess_le_neg_on_ball g f hf o hC.le hR hthird hcenter _ x hx v
  have h := (le_div_iff₀ hC).mp hradius
  nlinarith

end Yau.Proofs.C05HessianPropagationAux

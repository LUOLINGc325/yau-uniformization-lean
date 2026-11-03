import Yau.Proofs.C05RicciPropagationSegment

/-! Space propagation of physical real Ricci coercivity from a first-jet bound. -/
noncomputable section
open scoped Topology Manifold
namespace Yau.Proofs.C05RicciPropagationAux
open Yau Yau.Proofs.C05Aux Yau.Proofs.C05GradientFlowAux
variable {n : ℕ} {M : ComplexManifold n}

theorem ricciQuad_lower_bound_on_ball
    (g : SmoothMetric M) (o : M.Carrier) {C R μ : ℝ}
    (hC : 0 ≤ C) (hR : 0 < R)
    (hD : ∀ x ∈ distBall g.form o R, realRicciJetNorm g.form 1 x ≤ C)
    (hcenter : ∀ w : TangentVector M o, μ * realNormSq g.form o w ≤ ricciQuad g.form o w)
    (x : M.Carrier) (hx : x ∈ distBall g.form o R) (v : TangentVector M x) :
    (μ - C * inducedDistance g.form o x) * realNormSq g.form x v ≤
      ricciQuad g.form x v := by
  obtain ⟨w,hw,hbound⟩ := exists_center_vector_ricci_difference_le g o hC hR hD x hx v
  have hc := hcenter w
  rw [hw] at hc
  have hsub := (abs_le.mp hbound).1
  nlinarith

theorem ricciQuad_coercive_on_ball
    (g : SmoothMetric M) (o : M.Carrier) {C R μ : ℝ}
    (hC : 0 ≤ C) (hR : 0 < R) (hμ : 0 < μ)
    (hD : ∀ x ∈ distBall g.form o R, realRicciJetNorm g.form 1 x ≤ C)
    (hcenter : ∀ w : TangentVector M o, μ * realNormSq g.form o w ≤ ricciQuad g.form o w)
    (hsmall : C * R ≤ μ / 2)
    (x : M.Carrier) (hx : x ∈ distBall g.form o R) (v : TangentVector M x) :
    (μ / 2) * realNormSq g.form x v ≤ ricciQuad g.form x v := by
  have h := ricciQuad_lower_bound_on_ball g o hC hR hD hcenter x hx v
  have hd := (Yau.LeafProofs.L12Aux.mem_distBall_iff g o x hR).mp hx
  have hcd : C * inducedDistance g.form o x ≤ μ / 2 :=
    (mul_le_mul_of_nonneg_left hd.le hC).trans hsmall
  exact (mul_le_mul_of_nonneg_right (by linarith : μ / 2 ≤ μ - C * inducedDistance g.form o x)
    (realNormSq_nonneg g.form x v)).trans h

end Yau.Proofs.C05RicciPropagationAux

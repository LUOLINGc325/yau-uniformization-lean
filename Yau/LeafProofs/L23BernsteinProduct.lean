import Yau.LeafProofs.L23BernsteinCompact

/-! The actual parabolic product F=(16B+v)w and its negative quadratic term. -/

noncomputable section
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem bernstein_product_evolution
    (h : ℝ → HermitianField M) (σ B Dk Ek : ℝ)
    (v w : M.Carrier → ℝ → ℝ) (q : M.Carrier) (t z : ℝ)
    (hσ : 0 < σ) (hB : 1 ≤ B) (hDk : 0 ≤ Dk) (hEk : 0 ≤ Ek)
    (hv0 : 0 ≤ v q t) (hvB : v q t ≤ B) (hw : 0 ≤ w q t) (hz : 0 ≤ z)
    (hvSpace : ContDiffAt ℝ 2 (inChart q (fun y => v y t)) (chartPt q q))
    (hwSpace : ContDiffAt ℝ 2 (inChart q (fun y => w y t)) (chartPt q q))
    (hvTime : DifferentiableAt ℝ (v q) t) (hwTime : DifferentiableAt ℝ (w q) t)
    (hvOp : flowOp h σ v q t ≤ -σ*w q t+σ*Ek)
    (hwOp : flowOp h σ w q t ≤ -σ*z+σ*Dk*(1+w q t))
    (hvGrad : realGradPair (h t) (fun y => v y t) (fun y => v y t) q ≤ 4*v q t*w q t)
    (hwGrad : realGradPair (h t) (fun y => w y t) (fun y => w y t) q ≤ 4*w q t*z) :
    flowOp h σ (fun y s => (16*B+v y s)*w y s) q t ≤
      -σ/(4*(17*B)^2)*((16*B+v q t)*w q t)^2+
        σ*((17*B*Dk+Ek)^2+17*B*Dk) := by
  have hCS := realGradPair_cauchySchwarz (h t) (fun y => v y t) (fun y => w y t) q
  have hcross : realGradPair (h t) (fun y => v y t) (fun y => w y t) q^2 ≤
      16*v q t*(w q t)^2*z := by
    have hm := mul_le_mul hvGrad hwGrad
      (realGradPair_self_nonneg (h t) (fun y => w y t) q)
      (by positivity : 0 ≤ 4*v q t*w q t)
    nlinarith [hCS,hm]
  have hProduct := flowOp_mul h σ (fun y s => 16*B+v y s) w q t
    (contDiffAt_const.add hvSpace) hwSpace
    (hvTime.const_add (16*B)) hwTime
  rw [flowOp_const_add,realGradPair_const_add_left] at hProduct
  rw [hProduct]
  exact bernstein_negative_quadratic hB hv0 hvB hw hz hσ hDk hEk hvOp hwOp hcross

end Yau.LeafProofs.L23Aux

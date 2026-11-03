import Yau.LeafProofs.L23ScalarCalculus
import Yau.LeafProofs.L23BernsteinAlgebra

/-! The true scalar maximum argument, including the upper time face. -/

noncomputable section
open Filter
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem nonlinear_cutoff_pointwise
    (h : ℝ → HermitianField M) (σ b t α β G L : ℝ)
    (u ψ : M.Carrier → ℝ → ℝ) (q : M.Carrier)
    (hσ : 0 < σ) (hθ : 0 < t-b) (hu : 0 ≤ u q t) (hψ : 0 < ψ q t)
    (huSpace : ContDiffAt ℝ 2 (inChart q (fun y => u y t)) (chartPt q q))
    (hψSpace : ContDiffAt ℝ 2 (inChart q (fun y => ψ y t)) (chartPt q q))
    (huTime : DifferentiableAt ℝ (u q) t) (hψTime : DifferentiableAt ℝ (ψ q) t)
    (hSpaceMax : IsLocalMax
      (fun z => inChart q (fun y => ψ y t) z*inChart q (fun y => u y t) z) (chartPt q q))
    (hTimeMax : IsLocalMaxOn (fun s => (s-b)*ψ q s*u q s) (Set.Iic t) t)
    (hGrad : realGradPair (h t) (fun y => ψ y t) (fun y => ψ y t) q ≤ G*ψ q t)
    (huOp : flowOp h σ u q t ≤ -σ*α*(u q t)^2+σ*β)
    (hψOp : flowOp h σ ψ q t ≤ L) :
    0 ≤ ψ q t*u q t+(t-b)*ψ q t*(-σ*α*(u q t)^2+σ*β)+
      (t-b)*u q t*(L+σ*G) := by
  have hD := (((hasDerivAt_id t).sub_const b).mul hψTime.hasDerivAt).mul huTime.hasDerivAt
  have htime := L19Aux.hasDerivAt_nonneg_at_left_max hD hTimeMax
  simp only [one_mul,Pi.mul_apply,id_eq] at htime
  have hLap := chartRealLaplacian_nonpos_at_local_max (h t) q
    (hψSpace.mul huSpace) hSpaceMax
  rw [chartRealLaplacian_mul (h t) q hψSpace huSpace,
    inChart_center,inChart_center] at hLap
  change ψ q t*realLap (h t) (fun y => u y t) q+
    u q t*realLap (h t) (fun y => ψ y t) q+
      2*realGradPair (h t) (fun y => ψ y t) (fun y => u y t) q ≤ 0 at hLap
  have hzero := chartGradientPair_product_at_local_max (h t) q
    (hψSpace.differentiableAt (by norm_num)) (huSpace.differentiableAt (by norm_num))
    hSpaceMax (inChart q (fun y => ψ y t))
  rw [inChart_center,inChart_center] at hzero
  change ψ q t*realGradPair (h t) (fun y => ψ y t) (fun y => u y t) q+
    u q t*realGradPair (h t) (fun y => ψ y t) (fun y => ψ y t) q=0 at hzero
  have hcross : -realGradPair (h t) (fun y => ψ y t) (fun y => u y t) q ≤ u q t*G := by
    apply (mul_le_mul_iff_left₀ hψ).mp
    have hh := mul_le_mul_of_nonneg_left hGrad hu
    nlinarith [hzero]
  have hLapMul := mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (div_nonneg hσ.le (by norm_num : (0 : ℝ) ≤ 2)) hθ.le) hLap
  have hpoint : 0 ≤ ψ q t*u q t+(t-b)*
      (ψ q t*flowOp h σ u q t+u q t*flowOp h σ ψ q t-
        σ*realGradPair (h t) (fun y => ψ y t) (fun y => u y t) q) := by
    unfold flowOp
    nlinarith [htime,hLapMul]
  have h1 := mul_le_mul_of_nonneg_left huOp (mul_nonneg hθ.le hψ.le)
  have h2 := mul_le_mul_of_nonneg_left hψOp (mul_nonneg hθ.le hu)
  have h3 := mul_le_mul_of_nonneg_left hcross (mul_nonneg hθ.le hσ.le)
  nlinarith [hpoint,h1,h2,h3]

theorem nonlinear_cutoff_quadratic {σ α β Λ θ δ e U : ℝ}
    (hσ : 0 < σ) (hα : 0 < α) (hβ : 0 ≤ β) (hΛ : 0 ≤ Λ)
    (hθ : 0 < θ) (hθδ : θ ≤ δ) (he : 0 < e) (he1 : e ≤ 1) (hU : 0 ≤ U)
    (hpoint : 0 ≤ e*U+θ*e*(-σ*α*U^2+σ*β)+θ*U*Λ) :
    σ*α*(θ*e*U)^2 ≤ (1+Λ*δ)*(θ*e*U)+σ*β*δ^2 := by
  have hW : 0 ≤ θ*e*U := by positivity
  have heW : e*(θ*e*U) ≤ θ*e*U := by nlinarith
  have hθe : 0 ≤ θ*e := by positivity
  have hθeδ : θ*e ≤ δ := by nlinarith
  have hsquare := mul_self_le_mul_self hθe hθeδ
  have hsource := mul_le_mul_of_nonneg_left hsquare (mul_nonneg hσ.le hβ)
  have htime := mul_le_mul_of_nonneg_right hθδ (mul_nonneg hΛ hW)
  have hmain := mul_nonneg hθe hpoint
  nlinarith [heW,hsource,htime,hmain]

theorem nonlinear_maximum_bound_of_quadratic {σ α β Λ δ W : ℝ}
    (hσ : 0 < σ) (hα : 0 < α) (hβ : 0 ≤ β) (hΛ : 0 ≤ Λ)
    (hδ : 0 < δ) (hW : 0 ≤ W)
    (hquad : σ*α*W^2 ≤ (1+Λ*δ)*W+σ*β*δ^2) :
    W/δ ≤ 2*(1+Λ*δ)/(σ*α*δ)+Real.sqrt (2*β/α) := by
  let X := W/δ
  have hδX : δ*X=W := by dsimp only [X]; field_simp
  have hnorm : σ*α*X^2 ≤ ((1+Λ*δ)/δ)*X+σ*β := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hδ)).mp
    have hleft : (σ*α*X^2)*δ^2=σ*α*W^2 := by rw [←hδX]; ring
    have hright : (((1+Λ*δ)/δ)*X+σ*β)*δ^2=(1+Λ*δ)*W+σ*β*δ^2 := by
      rw [←hδX]
      field_simp
    rwa [hleft,hright]
  have hb := quadratic_maximum_bound (a := σ*α) (b := (1+Λ*δ)/δ) (c := σ*β) (W := X)
    (by positivity) (by positivity) (by positivity) (by dsimp only [X]; positivity) hnorm
  have harg : 2*(σ*β)/(σ*α)=2*β/α := by field_simp
  rw [harg] at hb
  change X ≤ _
  convert hb using 1
  congr 1
  field_simp

end Yau.LeafProofs.L23Aux

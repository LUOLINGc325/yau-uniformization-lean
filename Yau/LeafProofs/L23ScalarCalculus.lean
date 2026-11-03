import Yau.LeafProofs.L23TensorAlgebra
import Yau.LeafProofs.L19LocalizationMaximum

/-! Real Levi-Civita scalar calculus without a Kähler or completeness assumption. -/

noncomputable section
open Filter
open scoped Topology ContDiff Matrix Manifold

namespace Yau.LeafProofs.L23Aux

open L18Aux L19Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem inChart_center {α : Type*} (q : M.Carrier) (f : M.Carrier → α) :
    inChart q f (chartPt q q)=f q := by
  exact congrArg f ((extChartAt (ComplexModel n) q).left_inv (mem_extChartAt_source q))

theorem chartGradientPair_product_at_local_max (h : HermitianField M) (a : M.Carrier)
    {f k : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : DifferentiableAt ℝ f z) (hk : DifferentiableAt ℝ k z)
    (hm : IsLocalMax (fun w => f w*k w) z) (v : ComplexVector n → ℝ) :
    f z*chartGradientPair h a v k z+k z*chartGradientPair h a v f z=0 := by
  have hzero : chartGradientPair h a v (fun w => f w*k w) z=0 := by
    simp only [chartGradientPair_eq_sum,rDeriv,hm.fderiv_eq_zero,zero_apply,
      mul_zero,Finset.sum_const_zero]
  rw [chartGradientPair_symm h a v _ z,chartGradientPair_mul_left h a v hf hk,
    chartGradientPair_symm h a k v z,chartGradientPair_symm h a f v z] at hzero
  exact hzero

theorem chartCovHessian_mul (h : HermitianField M) (a : M.Carrier)
    {f k : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hk : ContDiffAt ℝ 2 k z) (i j : RIdx n) :
    chartCovHessian h a (fun w => f w*k w) z i j =
      f z * chartCovHessian h a k z i j +
        k z * chartCovHessian h a f z i j +
          rDeriv f z i * rDeriv k z j + rDeriv k z i * rDeriv f z j := by
  unfold chartCovHessian
  rw [rDeriv_rDeriv_eq_hessian (hf.mul hk), rDeriv_rDeriv_eq_hessian hf,
    rDeriv_rDeriv_eq_hessian hk, secondFDeriv_mul hf hk]
  simp_rw [rDeriv_mul (hf.differentiableAt (by norm_num))
    (hk.differentiableAt (by norm_num))]
  simp only [rDeriv, mul_add, Finset.sum_add_distrib, mul_sub, Finset.mul_sum]
  have hsum1 : (∑ x, christoffel h a z x i j * (fderiv ℝ f z (realVec x) * k z)) =
      ∑ x, k z * (christoffel h a z x i j * fderiv ℝ f z (realVec x)) := by
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hsum2 : (∑ x, christoffel h a z x i j * (f z * fderiv ℝ k z (realVec x))) =
      ∑ x, f z * (christoffel h a z x i j * fderiv ℝ k z (realVec x)) := by
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsum1, hsum2]
  ring

theorem chartRealLaplacian_mul (h : HermitianField M) (a : M.Carrier)
    {f k : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hk : ContDiffAt ℝ 2 k z) :
    chartRealLaplacian h a (fun w => f w*k w) z =
      f z * chartRealLaplacian h a k z +
        k z * chartRealLaplacian h a f z + 2*chartGradientPair h a f k z := by
  have hpoint (i j : RIdx n) := chartCovHessian_mul h a hf hk i j
  have hsplit : chartRealLaplacian h a (fun w => f w*k w) z =
      f z * chartRealLaplacian h a k z +
        k z * chartRealLaplacian h a f z +
          chartGradientPair h a f k z + chartGradientPair h a k f z := by
    simp only [chartRealLaplacian, chartGradientPair_eq_sum, hpoint,
      mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_left_comm, mul_assoc]
  rw [hsplit, chartGradientPair_symm h a k f z]
  ring

theorem chartRealLaplacian_const_add (h : HermitianField M) (a : M.Carrier)
    (C : ℝ) (f : ComplexVector n → ℝ) (z : ComplexVector n) :
    chartRealLaplacian h a (fun w => C+f w) z=chartRealLaplacian h a f z := by
  simp only [chartRealLaplacian,chartCovHessian,rDeriv,fderiv_const_add]

theorem realLap_mul (h : HermitianField M) (q : M.Carrier) (f g : M.Carrier → ℝ)
    (hf : ContDiffAt ℝ 2 (inChart q f) (chartPt q q))
    (hg : ContDiffAt ℝ 2 (inChart q g) (chartPt q q)) :
    realLap h (fun y => f y*g y) q=f q*realLap h g q+g q*realLap h f q+
      2*realGradPair h f g q := by
  unfold realLap realGradPair
  change chartRealLaplacian h q (fun z => inChart q f z*inChart q g z) (chartPt q q)=_
  rw [chartRealLaplacian_mul h q hf hg,inChart_center,inChart_center]

theorem flowOp_const_add (h : ℝ → HermitianField M) (σ C : ℝ)
    (u : M.Carrier → ℝ → ℝ) (q : M.Carrier) (t : ℝ) :
    flowOp h σ (fun y s => C+u y s) q t=flowOp h σ u q t := by
  unfold flowOp realLap
  change deriv (fun s => C+u q s) t-
    σ/2*chartRealLaplacian (h t) q (fun z => C+inChart q (fun y => u y t) z) (chartPt q q)=_
  rw [deriv_const_add,chartRealLaplacian_const_add]

theorem realGradPair_const_add_left (h : HermitianField M) (C : ℝ)
    (u v : M.Carrier → ℝ) (q : M.Carrier) :
    realGradPair h (fun y => C+u y) v q=realGradPair h u v q := by
  unfold realGradPair
  change L18Aux.chartGradientPair h q (fun z => C+inChart q u z) (inChart q v) (chartPt q q)=_
  simp only [L18Aux.chartGradientPair_eq_sum,rDeriv,fderiv_const_add]

theorem realGradPair_self_nonneg (h : HermitianField M) (u : M.Carrier → ℝ) (q : M.Carrier) :
    0 ≤ realGradPair h u u q :=
  L18Aux.chartGradientPair_self_nonneg h q (mem_extChartAt_target q) (inChart q u)

theorem realGradPair_cauchySchwarz (h : HermitianField M) (u v : M.Carrier → ℝ) (q : M.Carrier) :
    realGradPair h u v q^2 ≤ realGradPair h u u q*realGradPair h v v q :=
  L19Aux.chartGradientPair_cauchySchwarz h q (mem_extChartAt_target q) (inChart q u) (inChart q v)

theorem flowOp_mul (h : ℝ → HermitianField M) (σ : ℝ)
    (u v : M.Carrier → ℝ → ℝ) (q : M.Carrier) (t : ℝ)
    (hu : ContDiffAt ℝ 2 (inChart q (fun y => u y t)) (chartPt q q))
    (hv : ContDiffAt ℝ 2 (inChart q (fun y => v y t)) (chartPt q q))
    (huTime : DifferentiableAt ℝ (u q) t) (hvTime : DifferentiableAt ℝ (v q) t) :
    flowOp h σ (fun y s => u y s*v y s) q t=
      u q t*flowOp h σ v q t+v q t*flowOp h σ u q t-
        σ*realGradPair (h t) (fun y => u y t) (fun y => v y t) q := by
  unfold flowOp
  change deriv (fun s => u q s*v q s) t-
    σ/2*realLap (h t) (fun y => u y t*v y t) q=_
  rw [deriv_fun_mul huTime hvTime,realLap_mul (h t) q _ _ hu hv]
  ring

theorem chartRealLaplacian_nonpos_at_local_max (h : HermitianField M) (q : M.Carrier)
    {f : ComplexVector n → ℝ} (hf : ContDiffAt ℝ 2 f (chartPt q q))
    (hm : IsLocalMax f (chartPt q q)) :
    chartRealLaplacian h q f (chartPt q q) ≤ 0 := by
  letI := L12Aux.underlyingRealTangentNormedAddCommGroup h q
  letI := L12Aux.underlyingRealTangentInnerProductSpace h q
  let b := stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) q)
  rw [chartRealLaplacian_eq_orthonormal_covHessian h q hf b]
  apply Finset.sum_nonpos
  intro i _
  rw [hm.fderiv_eq_zero]
  simp only [ContinuousLinearMap.zero_apply,sub_zero]
  exact secondFDeriv_nonpos_at_local_max hf hm _

end Yau.LeafProofs.L23Aux

import Yau.LeafProofs.L23LocalDistanceSupport

/-! Pointwise real scalar chain rules used by the moving distance cutoff. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold Matrix
namespace Yau.LeafProofs.L23Aux
open L12Aux L18Aux L19Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem distanceSupport_chartGrad_scalar_comp
    (h : HermitianField M) (x : M.Carrier)
    {f : ComplexVector n → ℝ} {F : ℝ → ℝ} {z : ComplexVector n}
    (hf : DifferentiableAt ℝ f z) (hF : DifferentiableAt ℝ F (f z)) :
    chartGradientPair h x (F ∘ f) (F ∘ f) z =
      deriv F (f z) ^ 2 * chartGradientPair h x f f z := by
  rw [chartGradientPair_scalar_comp_left h x _ hf hF,
    chartGradientPair_symm h x f (F ∘ f),
    chartGradientPair_scalar_comp_left h x f hf hF]
  ring

theorem distanceSupport_chartHessian_scalar_comp
    (h : HermitianField M) (x : M.Carrier)
    {f : ComplexVector n → ℝ} {F : ℝ → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hF : ContDiffAt ℝ 2 F (f z)) (i j : RIdx n) :
    chartCovHessian h x (F ∘ f) z i j =
      deriv F (f z) * chartCovHessian h x f z i j +
        deriv (deriv F) (f z) * rDeriv f z i * rDeriv f z j := by
  have hfd := hf.differentiableAt (by norm_num)
  have hFd := hF.differentiableAt (by norm_num)
  have hsum : (∑ k, christoffel h x z k i j * rDeriv (F ∘ f) z k) =
      deriv F (f z) * ∑ k, christoffel h x z k i j * rDeriv f z k := by
    simp_rw [rDeriv_scalar_comp hfd hFd]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp only [chartCovHessian, L18Aux.rDeriv_rDeriv_eq_hessian (hF.comp z hf),
    L18Aux.rDeriv_rDeriv_eq_hessian hf]
  rw [secondFDeriv_comp hf hF, secondFDeriv_scalar_apply hF, hsum]
  simp only [fderiv_eq_deriv_mul, rDeriv]
  ring

theorem distanceSupport_chartLap_scalar_comp
    (h : HermitianField M) (x : M.Carrier)
    {f : ComplexVector n → ℝ} {F : ℝ → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hF : ContDiffAt ℝ 2 F (f z)) :
    chartRealLaplacian h x (F ∘ f) z =
      deriv F (f z) * chartRealLaplacian h x f z +
        deriv (deriv F) (f z) * chartGradientPair h x f f z := by
  simp only [chartRealLaplacian, chartGradientPair_eq_sum,
    distanceSupport_chartHessian_scalar_comp h x hf hF, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem distanceSupport_jointC2_space {E : M.Carrier → ℝ → ℝ}
    {x : M.Carrier} {t : ℝ}
    (hE : ContDiffAt ℝ 2
      (fun z : ComplexVector n × ℝ => E (chartInv x z.1) z.2) (chartPt x x,t)) :
    ContDiffAt ℝ 2 (inChart x (fun y => E y t)) (chartPt x x) := by
  exact hE.comp (chartPt x x)
    (show ContDiffAt ℝ 2 (fun z : ComplexVector n => (z,t)) (chartPt x x) from
      contDiffAt_id.prodMk contDiffAt_const)

theorem distanceSupport_jointC2_time {E : M.Carrier → ℝ → ℝ}
    {x : M.Carrier} {t : ℝ}
    (hE : ContDiffAt ℝ 2
      (fun z : ComplexVector n × ℝ => E (chartInv x z.1) z.2) (chartPt x x,t)) :
    ContDiffAt ℝ 2 (E x) t := by
  have hc := hE.comp t
    (show ContDiffAt ℝ 2 (fun s : ℝ => (chartPt x x,s)) t from
      contDiffAt_const.prodMk contDiffAt_id)
  change ContDiffAt ℝ 2 (fun s => E (chartInv x (chartPt x x)) s) t at hc
  have hinv : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  rw [hinv] at hc
  exact hc

theorem distanceSupport_flowOp_scalar_comp
    (h : ℝ → HermitianField M) (σ : ℝ) {E : M.Carrier → ℝ → ℝ}
    {F : ℝ → ℝ} {x : M.Carrier} {t : ℝ}
    (hE : ContDiffAt ℝ 2
      (fun z : ComplexVector n × ℝ => E (chartInv x z.1) z.2) (chartPt x x,t))
    (hF : ContDiffAt ℝ 2 F (E x t)) :
    flowOp h σ (fun y s => F (E y s)) x t =
      deriv F (E x t) * flowOp h σ E x t -
        (σ/2) * deriv (deriv F) (E x t) *
          realGradPair (h t) (fun y => E y t) (fun y => E y t) x := by
  have hv : inChart x (fun y => E y t) (chartPt x x) = E x t :=
    congrArg (fun y => E y t) ((extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x))
  have hspace := distanceSupport_jointC2_space hE
  have htime := distanceSupport_jointC2_time hE
  have hF' : ContDiffAt ℝ 2 F (inChart x (fun y => E y t) (chartPt x x)) := hv.symm ▸ hF
  have hchain := distanceSupport_chartLap_scalar_comp (h t) x hspace hF'
  rw [hv] at hchain
  unfold flowOp realLap realGradPair
  change deriv (F ∘ E x) t - (σ/2) *
    chartRealLaplacian (h t) x (F ∘ inChart x (fun y => E y t)) (chartPt x x) = _
  rw [deriv_comp t (hF.differentiableAt (by norm_num)) (htime.differentiableAt (by norm_num)), hchain]
  ring

end Yau.LeafProofs.L23Aux

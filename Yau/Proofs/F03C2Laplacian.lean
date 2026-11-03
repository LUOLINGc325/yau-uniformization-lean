import Yau.Proofs.F03PointwiseMaximum

/-! Local C² linearity of the frozen actual scalar Laplacian. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L18Aux LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem secondFDeriv_const_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (f : E → ℝ) (z v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => a * f y)) z v w =
      a * fderiv ℝ (fderiv ℝ f) z v w := by
  change fderiv ℝ (fderiv ℝ (a • f)) z v w = _
  rw [fderiv_const_smul_field a]
  have he := fderiv_const_smul_field (𝕜 := ℝ) (f := fderiv ℝ f) a
  exact congrArg (fun F : E → E →L[ℝ] (E →L[ℝ] ℝ) => F z v w) he

variable {n : ℕ} {M : ComplexManifold n}

theorem laplacian_c2_principal (g : HermitianField M) (u : M.Carrier → ℝ) (x : M.Carrier)
    (hu : ContDiffAt ℝ 2 (inChart x u) (chartPt x x)) :
    (∑ i, ∑ j, (realMetricFn g x (chartPt x x))⁻¹ i j *
      fderiv ℝ (fderiv ℝ (inChart x u)) (chartPt x x) (realVec i) (realVec j)) =
        2 * laplacian g u x := by
  exact principal_realLaplacian_eq_twice_traceWith g x (mem_extChartAt_target x) hu

theorem laplacian_c2_linear_combination (g : HermitianField M)
    (u v : M.Carrier → ℝ) (x : M.Carrier)
    (hu : ContDiffAt ℝ 2 (inChart x u) (chartPt x x))
    (hv : ContDiffAt ℝ 2 (inChart x v) (chartPt x x)) (a b : ℝ) :
    laplacian g (fun y => a * u y + b * v y) x =
      a * laplacian g u x + b * laplacian g v x := by
  have huc : ContDiffAt ℝ 2 (fun z => a * inChart x u z) (chartPt x x) :=
    contDiffAt_const.mul hu
  have hvc : ContDiffAt ℝ 2 (fun z => b * inChart x v z) (chartPt x x) :=
    contDiffAt_const.mul hv
  have hc : ContDiffAt ℝ 2 (inChart x (fun y => a * u y + b * v y)) (chartPt x x) :=
    huc.add hvc
  have heq : 2 * laplacian g (fun y => a * u y + b * v y) x =
      a * (2 * laplacian g u x) + b * (2 * laplacian g v x) := by
    rw [← laplacian_c2_principal g _ x hc, ← laplacian_c2_principal g u x hu,
      ← laplacian_c2_principal g v x hv, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    change (realMetricFn g x (chartPt x x))⁻¹ i j *
      fderiv ℝ (fderiv ℝ (fun z => a * inChart x u z + b * inChart x v z))
        (chartPt x x) (realVec i) (realVec j) = _
    rw [secondFDeriv_add_local huc hvc, secondFDeriv_const_mul, secondFDeriv_const_mul]
    ring
  linarith only [heq]

end Yau.Proofs.F03Aux

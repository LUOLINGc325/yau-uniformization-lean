import Yau.LeafProofs.L17PhysicalGaussianResidual
import Yau.LeafProofs.L17LocalizedSchauderRawSum

/-! The actual finite-overlap global Holder element of the Gaussian residual. -/

open Set Metric
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux

open Yau.Parabolic L17HolderAux L17LocalizedSchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def gaussianResidualFun (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (q : Cylinder M T) : ℝ :=
  ∑ᶠ p,rawLocalizedTerm P T p (physicalGaussianResidual P T hT f p) q

theorem exists_uniform_gaussian_residual_holder_budget (A : BoundedChartFamily g) (hg : MetricSmooth g)
    (N : ℕ) (γ : ℝ) (hγ : 0 < γ) :
    ∃ L : ℝ, 0 < L ∧ ∀ (P : UniformChartPartition g), P.charts = A → P.overlapBudget ≤ N →
      P.radius ≤ 1 → 2*P.radius < A.radius → ∀ (T : ℝ) (hT : 0 ≤ T) (C : ℝ), 0 ≤ C →
      ∀ f : HolderSpace P T γ,
      (∀ p : P.centers, HolderBound γ (cylinder (ball (0 : Space n) 2) 0 (T/P.radius^2))
        (unitGaussianResidual P T hT f p) C) →
      ∃! e : HolderSpace P T γ, holderFun e = gaussianResidualFun P T hT f ∧ ‖e‖ ≤ L*C := by
  obtain ⟨L,hL,hRaw⟩ := exists_uniform_raw_sum_holder A hg N γ hγ.le
  refine ⟨3*L,mul_pos (by norm_num) hL,?_⟩
  intro P hA hN hρ1 hρA T hT C hC f hUnit
  have hρP : 2*P.radius < P.charts.radius := by simpa only [hA] using hρA
  have hProfile (p : P.centers) := physicalGaussianResidual_profile P T hT hγ f p (hUnit p)
  have h := hRaw P hA hN hρ1 hρA T C (2*C) hC (mul_nonneg (by norm_num) hC)
    (physicalGaussianResidual P T hT f)
    (fun p => (hProfile p).1) (fun p z hz t => physicalGaussianResidual_zero_outside P T hT hρP f p z hz t)
    (fun p z hz t => (hProfile p).2.1 (z,t) ⟨hz,mem_univ _⟩)
    (fun p z w hz hw t s => (hProfile p).2.2 (z,t) ⟨hz,mem_univ _⟩ (w,s) ⟨hw,mem_univ _⟩)
  have hConst : L*(C+2*C) = (3*L)*C := by ring
  change ∃! e : HolderSpace P T γ,
    holderFun e = (fun q => ∑ᶠ p,rawLocalizedTerm P T p (physicalGaussianResidual P T hT f p) q) ∧ ‖e‖ ≤ (3*L)*C
  simpa only [hConst] using h

end Yau.LeafProofs.L17Aux

import Yau.Proofs.F01ShiftedAffineTensorHolder
import Yau.Proofs.F01ShiftedNativePotential
import Yau.Proofs.F01ComplexBackgroundHolder
import Yau.Proofs.F01AffineParabolicHolder

/-! All true spatial jets of the shifted native background have a
common family of parabolic Holder budgets on any fixed finite horizon.
The family precedes the center, scale and clock center. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem shifted_background_spatial_tensor_holder_budgets
    (A : BoundedChartFamily g) {β T : ℝ} (hT : 0 ≤ T) (hβ : β ≤ 1) :
    ∃ K : ℕ → ℝ, (∀ k, 0 < K k) ∧
      ∀ k (ρ τ : ℝ), 0 < ρ → ρ ≤ A.radius → ρ ≤ 1 → |τ| ≤ T → ∀ a : M.Carrier,
      HolderBound β (cylinder (ball (0 : Space n) 1) (-1) 1)
        (fun p => iteratedFDeriv ℝ k (fun z => shiftedComplexBackground A a ρ τ (z, p.2)) p.1) (K k) := by
  have each : ∀ k : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ (ρ τ : ℝ), 0 < ρ → ρ ≤ A.radius → ρ ≤ 1 → |τ| ≤ T → ∀ a : M.Carrier,
      HolderBound β (cylinder (ball (0 : Space n) 1) (-1) 1)
        (fun p => iteratedFDeriv ℝ k (fun z => shiftedComplexBackground A a ρ τ (z, p.2)) p.1) K := by
    intro k
    obtain ⟨K, hK, hBudget⟩ := shifted_affine_spatial_tensor_holder_budget k hT
      (background_matrix_frobenius_uniform_jets A (k + 1))
      (backgroundRicci_frobenius_uniform_jets A (k + 1))
      (background_matrix_frobenius_smooth A) (backgroundRicci_frobenius_smooth A) hβ
    refine ⟨K, hK, ?_⟩
    intro ρ τ hρ hρr hρ1 hτ a
    have hSlope : |-(ρ ^ 2)| ≤ 1 := by
      rw [abs_neg, abs_of_nonneg (sq_nonneg _)]
      nlinarith
    have hb := hBudget ρ (-τ) (-(ρ ^ 2)) hρ hρr hρ1 (by simpa only [abs_neg] using hτ) hSlope a
    have he (t : ℝ) : (fun z : Space n => shiftedComplexBackground A a ρ τ (z, t)) =
        fun z => pullbackMatrix g (A.chart a) (ρ • z) +
          (-τ + -(ρ ^ 2) * t) • backgroundRicci (pullbackMatrix g (A.chart a)) (ρ • z) := by
      funext z
      simp only [shiftedComplexBackground, chartAffineBackground, affineParabolicPoint, add_zero,
        Complex.coe_smul]
      module
    apply holderBound_congr_on_native hb
    intro p hp
    exact congrArg (fun f : Space n → Matrix (Fin n) (Fin n) ℂ => iteratedFDeriv ℝ k f p.1) (he p.2).symm
  choose K hK hk using each
  exact ⟨K, hK, hk⟩

theorem shiftedComplexBackground_smooth_spatial_slice (A : BoundedChartFamily g)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (τ : ℝ) (a : M.Carrier) (t : ℝ) :
    ContDiffOn ℝ ∞ (fun z => shiftedComplexBackground A a ρ τ (z, t)) (ball 0 1) := by
  have hd : ContDiffOn ℝ ∞ (fun z : Space n => ρ • z) (ball 0 1) := by fun_prop
  have hm := (background_matrix_frobenius_smooth A a).comp hd
    (fun z hz => spatialDilation_mem_ball hρ hρr hz)
  have hr := (backgroundRicci_frobenius_smooth A a).comp hd
    (fun z hz => spatialDilation_mem_ball hρ hρr hz)
  have hs := hm.sub (hr.const_smul (τ + ρ ^ 2 * t))
  simpa only [shiftedComplexBackground, chartAffineBackground, affineParabolicPoint,
    add_zero, Complex.coe_smul, Function.comp_apply] using hs

end Yau.NodeProofs.F01Aux

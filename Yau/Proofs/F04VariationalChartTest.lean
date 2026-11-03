import Yau.Proofs.F04ChartEnergyGlobalTime
import Yau.Proofs.F04VariationalMovingTest

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint Yau.Parabolic Yau.Proofs.F03Aux Yau.MassTargetStatements Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

local instance (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier) :
    CompleteSpace (DirichletEnergy g μ hμ Ω) := dirichletEnergy_completeSpace g μ hμ Ω

/-- The original variational solution admits every genuine compact spacetime
 chart test with its actual time derivative in the supported energy space. -/
theorem variationalSolution_chart_test
    (g : SmoothMetric M) (hg : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω K : Set M.Carrier)
    (hΩ : MeasurableSet Ω) (hK : IsCompact K) (hΩK : Ω ⊆ K)
    (c : M.Carrier) {O : Set (Space n)} (hOt : O ⊆ chartTarget c)
    (hMap : chartInv c '' O ⊆ Ω) {S : ℝ} (hS : 0 < S)
    (B : ℝ → DirichletEnergy g μ hμ Ω →L[ℝ] EnergyDual (DirichletEnergy g μ hμ Ω))
    (f : ℝ → FixedPivot μ Ω) (U : ℝ → DirichletEnergy g μ hμ Ω)
    (R : ℝ → EnergyDual (DirichletEnergy g μ hμ Ω)) (a : ℝ → FixedPivot μ Ω)
    (hSol : VariationalSolution μ Ω S (dirichletL2 g μ hμ Ω) B f U R a)
    {φ : Point n → ℝ} (hφ : Test (O ×ˢ Ioo 0 S) φ) :
    let Φ := fun t => dirichletCoreToEnergy g μ hμ Ω (chartSupportedTestCore g μ hμ Ω c hOt hMap hφ t)
    let Ψ := fun t => dirichletCoreToEnergy g μ hμ Ω
      (chartSupportedTestCore g μ hμ Ω c hOt hMap (test_timeDerivative hφ) t)
    (∫ t in Ioo 0 S, inner ℝ (a t) (dirichletL2 g μ hμ Ω (Ψ t)) - B t (U t) (Φ t) +
      inner ℝ (f t) (dirichletL2 g μ hμ Ω (Φ t))) = 0 := by
  let j := dirichletL2 g μ hμ Ω
  let Φ := fun t => dirichletCoreToEnergy g μ hμ Ω (chartSupportedTestCore g μ hμ Ω c hOt hMap hφ t)
  let Ψ := fun t => dirichletCoreToEnergy g μ hμ Ω
    (chartSupportedTestCore g μ hμ Ω c hOt hMap (test_timeDerivative hφ) t)
  obtain ⟨hΦ, hdΦ⟩ := chartSupportedTestCore_contDiff_one g hg μ hμ Ω K hΩ hK hΩK c hOt hMap hS hφ
  have hj : ‖j‖ ≤ 1 := j.opNorm_le_bound zero_le_one (fun u => by
    simpa only [one_mul] using dirichletL2_norm_le g μ hμ Ω u)
  have hm := variationalSolution_moving_test μ Ω hS j hj B f U R a hSol Φ hΦ
    0 ⟨le_rfl, hS.le⟩ S ⟨hS.le, le_rfl⟩
  have hD : deriv Φ = Ψ := funext (fun t => (hdΦ t).deriv)
  have h0 : Φ 0 = 0 := (chartSupportedTestCore_zero_germ g μ hμ Ω c hOt hMap hφ 0 (by simp)).eq_of_nhds
  have hS0 : Φ S = 0 := (chartSupportedTestCore_zero_germ g μ hμ Ω c hOt hMap hφ S (by simp)).eq_of_nhds
  simp only [h0, hS0, map_zero, inner_zero_right, sub_self, hD] at hm
  rw [intervalIntegral.integral_of_le hS.le, integral_Ioc_eq_integral_Ioo] at hm
  have hEq := hSol.2.2.2.2.2.2
  have hAE := hSol.2.2.2.2.1
  apply (integral_congr_ae ?_).trans hm.symm
  filter_upwards [hEq, hAE] with t ht hat
  have he := ht (Φ t)
  change inner ℝ (a t) (j (Ψ t)) - B t (U t) (Φ t) + inner ℝ (f t) (j (Φ t)) =
    R t (Φ t) + inner ℝ (j (U t)) (j (Ψ t))
  rw [hat]
  linarith only [he]

end Yau.F04Proof

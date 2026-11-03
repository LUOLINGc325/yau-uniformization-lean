import Yau.Proofs.F03ExhaustionStepL2
import Yau.Proofs.F03EulerUniformDomains

/-! Actual zero-extended Euler powers converge on the original given exhaustion. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem dirichletHeatEuler_ambient_eq (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) (t : ℝ) (ht : 0 < t) (k : ℕ) (f : Lp ℝ 2 μ) :
    l2ZeroExtension μ Ω hΩ (dirichletHeatEuler g μ hμ Ω t ht k (l2Restriction μ Ω f))=
      ((dirichletAmbientStep g μ hμ Ω hΩ (t/scalarEulerCount k)
        (div_pos ht (scalarEulerCount_cast_pos k)))^scalarEulerCount k) f := by
  have hN : 0 < scalarEulerCount k := by dsimp only [scalarEulerCount];positivity
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  unfold dirichletHeatEuler
  have hpow : m+1=scalarEulerCount k := hm.symm
  simpa only [hpow] using (dirichletAmbientStep_pow_succ g μ hμ Ω hΩ
    (div_pos ht (scalarEulerCount_cast_pos k)) m f).symm

theorem dirichletHeatEuler_exhaustion_tendsto (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {O : ℕ → Set M.Carrier} (hO : SmoothExhaustion O)
    (t : ℝ) (ht : 0 < t) (k : ℕ) (f : Lp ℝ 2 μ) :
    Tendsto (fun j => l2ZeroExtension μ (O j) (hO.1 j).1.measurableSet
      (dirichletHeatEuler g μ hμ (O j) t ht k (l2Restriction μ (O j) f))) atTop
      (𝓝 (scalarHeatEuler g μ hμ t ht k f)) := by
  have hlim := dirichletAmbientStep_powers_tendsto g μ hμ hO
    (div_pos ht (scalarEulerCount_cast_pos k)) (scalarEulerCount k) f
  simpa only [dirichletHeatEuler_ambient_eq,scalarHeatEuler] using hlim

theorem dirichletHeatEuler_ambient_error (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) (t : ℝ) (ht : 0 < t) (k : ℕ) (f : Lp ℝ 2 μ) :
    ‖l2ZeroExtension μ Ω hΩ (dirichletHeatEuler g μ hμ Ω t ht k (l2Restriction μ Ω f))-
      l2ZeroExtension μ Ω hΩ (dirichletHeat g μ hμ Ω t (l2Restriction μ Ω f))‖ ≤
      scalarEulerUniformError t ht k*‖f‖ := by
  rw [← map_sub,l2ZeroExtension_norm]
  change ‖(dirichletHeatEuler g μ hμ Ω t ht k-dirichletHeat g μ hμ Ω t) (l2Restriction μ Ω f)‖ ≤ _
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul (dirichletHeat_euler_uniform_bound g μ hμ Ω t ht k)
      (restrictL2_norm_le μ Ω f) (norm_nonneg _) (norm_nonneg _))

end Yau.Proofs.F03Aux

import Yau.LeafProofs.L19HeatAnnularScalarBounds

/-! Actual annular gradient energies from internally proved local Caccioppoli. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

/-- For radii at least one, a uniform expanded-annulus squared-scalar
bound gives the actual integrated gradient bound for either heat direction.
The Caccioppoli constant is selected before all geometric data. -/
theorem exists_uniform_annular_heat_energy_from_square_bound (n : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (M : ComplexManifold n) (g : SmoothMetric M), IsKahler g →
      ∀ (μ : Measure M.Carrier), IsRiemannianVolume g.form μ →
      ∀ (I : Set ℝ), IsOpen I → ∀ (u : M.Carrier → ℝ → ℝ), SmoothSpaceTime u I →
      ((∀ y t, t ∈ I → HasDerivAt (u y) (laplacian g.form (fun z => u z t) y) t) ∨
        (∀ y t, t ∈ I → HasDerivAt (u y) (-laplacian g.form (fun z => u z t) y) t)) →
      ∀ (o : M.Carrier) (R s T B : ℝ), 1 ≤ R → Icc s T ⊆ I → s ≤ T → 0 ≤ B →
      (∀ t ∈ Icc s T,
        (∫ x in {x | R / 2 ≤ inducedDistance g.form o x ∧ inducedDistance g.form o x ≤ 4 * R},
          u x t ^ 2 ∂μ) ≤ B) →
      (∫ t in s..T, ∫ x in {x | R ≤ inducedDistance g.form o x ∧ inducedDistance g.form o x ≤ 2 * R},
        scalarGradientPair g.form (fun y => u y t) (fun y => u y t) x ∂μ) ≤
        (2 + A * (T - s)) * B := by
  obtain ⟨A, hA, hCacci⟩ := LocalTime.exists_uniform_scalar_heat_annular_caccioppoli n
  refine ⟨A, hA, ?_⟩
  intro M g hK μ hμ I hI u hu hheat o R s T B hR hslab hsT hB hL2
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hreg := LocalTime.scalarHeat_annular_integrable hI g μ hμ hu o (R / 2) (4 * R) hslab hsT
  have htime : (∫ t in s..T, ∫ x in
      {x | R / 2 ≤ inducedDistance g.form o x ∧ inducedDistance g.form o x ≤ 4 * R},
        u x t ^ 2 ∂μ) ≤ (T - s) * B := by
    have hh := intervalIntegral.integral_mono_on hsT hreg.2.1
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => B) volume s T) hL2
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hh
  have hcoef : A / R ^ 2 ≤ A := by
    apply (div_le_iff₀ (pow_pos hR0 2)).mpr
    nlinarith [sq_nonneg (R - 1)]
  have hlast : 2 * B + (A / R ^ 2) * ((T - s) * B) ≤ (2 + A * (T - s)) * B := by
    have hh := mul_le_mul_of_nonneg_right hcoef (mul_nonneg (sub_nonneg.mpr hsT) hB)
    nlinarith only [hh]
  obtain ⟨hF, hBck⟩ := hCacci M g hK μ hμ I hI u hu o R hR0 s T hslab hsT
  rcases hheat with hheat | hheat
  · have hh := hF hheat
    have he := hL2 s ⟨le_rfl, hsT⟩
    have hb := mul_le_mul_of_nonneg_left htime (div_nonneg hA.le (sq_nonneg R))
    exact (show _ ≤ 2 * B + (A / R ^ 2) * ((T - s) * B) by linarith only [hh, he, hb]).trans hlast
  · have hh := hBck hheat
    have he := hL2 T ⟨hsT, le_rfl⟩
    have hb := mul_le_mul_of_nonneg_left htime (div_nonneg hA.le (sq_nonneg R))
    exact (show _ ≤ 2 * B + (A / R ^ 2) * ((T - s) * B) by linarith only [hh, he, hb]).trans hlast

end Yau.LeafProofs.L19Aux

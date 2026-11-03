import Yau.Proofs.V03JointGaussTwoForm
import Yau.Proofs.V03WithinDiscSlice
import Yau.Proofs.V03GaussDensity

/-! The spatial diagonal of the genuine joint Gauss two-form is the
original closed-disc Gauss density, including the circle. -/

open scoped Manifold Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem jointGaussTwoForm_spatial_diagonal {n q : ℕ} {M : ComplexManifold n}
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {f : ℂ × ℂ → CotangentPoint M} {U : Set ℂ}
    (hf : CotangentHolomorphicOn f (U ×ˢ Metric.closedBall (0 : ℂ) 1))
    {z ζ : ℂ} (hz : z ∈ U) (hζ : ζ ∈ Metric.closedBall (0 : ℂ) 1) :
    jointGaussTwoForm G f (U ×ˢ Metric.closedBall (0 : ℂ) 1) (z, ζ)
      ![((0, 1) : ℂ × ℂ), ((0, Complex.I) : ℂ × ℂ)] =
        gaussDensityWithin G (fun η => f (z, η)) ζ := by
  have hself : f (z, ζ) ∈ cotangentSource (f (z, ζ)).1 := mem_extChartAt_source _
  have hpot := (gaussPotential_contDiffAt hG (f (z, ζ)).1
    (cotangentChart_mapsTo (f (z, ζ)).1 hself)).of_le (show (2 : ℕ∞ω) ≤ ∞ by simp)
  have hcoord := (cotangentHolomorphicOn_centeredCoords_contDiffWithinAt (p := (z, ζ)) hf ⟨hz, hζ⟩).differentiableWithinAt (by simp)
  have hI : ((0, Complex.I) : ℂ × ℂ) = Complex.I • ((0, 1) : ℂ × ℂ) := by
    simp only [Prod.smul_mk, smul_eq_mul, mul_zero, mul_one]
  rw [jointGaussTwoForm, twoForm_pullback_apply, hI]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul]
  rw [scalarLeviTwoForm_diagonal hpot,
    ← fderivWithin_complex_disc_slice hz hζ hcoord 1]
  rfl

end Yau.Blueprint.V03Proof

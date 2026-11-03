import Yau.Proofs.V03JointBaseTwoForm
import Yau.Proofs.V03WithinDiscSlice
import Yau.Proofs.V03BaseDensity

/-! The original base-area density is precisely the spatial diagonal of
the genuine joint base two-form, including the original closed disc circle. -/

open scoped Manifold Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem jointBaseTwoForm_spatial_diagonal {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) {f : ℂ × ℂ → CotangentPoint M} {U : Set ℂ}
    (hf : CotangentHolomorphicOn f (U ×ˢ Metric.closedBall (0 : ℂ) 1))
    {z ζ : ℂ} (hz : z ∈ U) (hζ : ζ ∈ Metric.closedBall (0 : ℂ) 1) :
    jointBaseTwoForm h f (U ×ˢ Metric.closedBall (0 : ℂ) 1) (z, ζ)
      ![((0, 1) : ℂ × ℂ), ((0, Complex.I) : ℂ × ℂ)] =
        baseDensityWithin h (fun η => f (z, η)) ζ := by
  have hself : f (z, ζ) ∈ cotangentSource (f (z, ζ)).1 := mem_extChartAt_source _
  have hs : CotangentDisc (fun η => f (z, η)) :=
    (hf.comp (contDiff_const.prodMk contDiff_id) (fun η hη => ⟨hz, hη⟩)).cotangentDisc
  have hcoord : DifferentiableWithinAt ℂ (fun r => chartPt (f (z, ζ)).1 (f r).1)
      (U ×ˢ Metric.closedBall (0 : ℂ) 1) (z, ζ) :=
    (cotangentHolomorphicOn_centeredCoords_contDiffWithinAt
      (p := (z, ζ)) hf ⟨hz, hζ⟩).fst.differentiableWithinAt (by simp)
  rw [baseDensityWithin_eq_fixed_chart h hs hζ (f (z, ζ)).1 hself]
  have hI : ((0, Complex.I) : ℂ × ℂ) = Complex.I • ((0, 1) : ℂ × ℂ) := by
    simp only [Prod.smul_mk, smul_eq_mul, mul_zero, mul_one]
  rw [jointBaseTwoForm, twoForm_pullback_apply, hI]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul]
  rw [chartKahlerTwoForm, matrixKahlerTwoForm_diagonal (hMat_isHermitian h _ _),
    ← fderivWithin_complex_disc_slice hz hζ hcoord 1]
  rfl

end Yau.Blueprint.V03Proof

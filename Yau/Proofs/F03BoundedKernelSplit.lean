import Yau.Proofs.F03BoundedKernelAlgebra
import Yau.Proofs.F03BoundedHeatLocalization

/-! The original bounded heat splits exactly into its actual compact and far source evolutions. -/
noncomputable section
open MeasureTheory Filter Set
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings HeatTargetCandidates LeafProofs.L18Aux LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem dirichletMinimalBoundedHeat_cutoff_split
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (f : M.Carrier → ℝ) (hf : AEStronglyMeasurable f μ)
    (B : ℝ) (hBound : ∀ y,|f y| ≤ B)
    (η : ScalarEnergyDomain g μ hμ) (hηrange : ∀ y,η y ∈ Icc (0 : ℝ) 1)
    {t : ℝ} (ht : 0 ≤ t) :
    boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO) f t=
      (fun x => boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO)
          (fun y => η y*f y) t x+
        boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO)
          (fun y => (1-η y)*f y) t x) := by
  have hη : AEStronglyMeasurable (fun y => η y) μ :=
    (continuous_of_smoothFn η.2.1).aestronglyMeasurable
  have hCompact : ∀ y,|η y*f y| ≤ B := by
    intro y
    rw [abs_mul,abs_of_nonneg (hηrange y).1]
    exact (mul_le_mul_of_nonneg_right (hηrange y).2 (abs_nonneg _)).trans (by simpa using hBound y)
  have hFar : ∀ y,|(1-η y)*f y| ≤ B := by
    intro y
    have hOne : |1-η y| ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr (hηrange y).2)]
      linarith [(hηrange y).1]
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hOne (abs_nonneg _)).trans (by simpa using hBound y)
  have hAdd := dirichletMinimalBoundedHeat_add g hK μ hμ O hO
    (fun y => η y*f y) (fun y => (1-η y)*f y) (hη.mul hf)
    ((aestronglyMeasurable_const.sub hη).mul hf) ⟨B,hCompact⟩ ⟨B,hFar⟩ ht
  have hData : (fun y => η y*f y+(1-η y)*f y)=f := by funext y;ring
  exact (congrArg (fun F => boundedKernelEvolution μ
    (dirichletMinimalKernelCandidate g hK μ hμ O hO) F t) hData.symm).trans hAdd

end Yau.Proofs.F03Aux

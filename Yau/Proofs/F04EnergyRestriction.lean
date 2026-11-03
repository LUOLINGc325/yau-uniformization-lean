import Yau.Proofs.F04FormMeasureRestriction
import Yau.Proofs.F04AmbientEnergy
import Yau.Proofs.F04PositiveIndicator

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03 Yau.LeafProofs.L19Aux

variable {n k : ℕ} {M : ComplexManifold n}

theorem scalarEnergyD_restrict_univ (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (q : ScalarEnergySpace g μ hμ) :
    formMeasureRestriction g (μ.restrict Set.univ) (μ.restrict O)
      (by simpa only [Measure.restrict_univ] using Measure.restrict_le_self) (scalarEnergyD g μ hμ Set.univ q) =
      scalarEnergyD g μ hμ O q := by
  let R := formMeasureRestriction (k := 1) g (μ.restrict Set.univ) (μ.restrict O)
    (by simpa only [Measure.restrict_univ] using Measure.restrict_le_self)
  refine UniformSpace.Completion.induction_on
    (p := fun q : ScalarEnergySpace g μ hμ => R (scalarEnergyD g μ hμ Set.univ q) =
      scalarEnergyD g μ hμ O q) q
    (isClosed_eq (R.continuous.comp (scalarEnergyD g μ hμ Set.univ).continuous)
      (scalarEnergyD g μ hμ O).continuous) ?_
  intro f
  rw [scalarEnergyD_coe, scalarEnergyD_coe]
  exact formMeasureRestriction_realize g _ _ _ _ _

/-- Active-set multiplication commutes with genuine measure restriction
whenever the scalar L2 representatives agree on the smaller measure. -/
theorem formMeasureRestriction_positive (g : SmoothMetric M) (μ ν : Measure M.Carrier)
    (hνμ : ν ≤ μ) (f : Lp ℝ 2 μ) (f' : Lp ℝ 2 ν)
    (hf : f' =ᵐ[ν] f) (a : L2FormHilbert g μ k) :
    formMeasureRestriction g μ ν hνμ (positiveFormMultiplier g μ f a) =
      positiveFormMultiplier g ν f' (formMeasureRestriction g μ ν hνμ a) := by
  obtain ⟨A, hA, hrep⟩ := l2FormHilbert_exists_section g μ a
  rw [← hrep, positiveFormMultiplier_realize, formMeasureRestriction_realize,
    formMeasureRestriction_realize, positiveFormMultiplier_realize]
  apply (realizeL2Form_eq_iff_ae g ν _ _).mpr
  filter_upwards [hf] with x hx
  change (if 0 < f x then A x else 0) = (if 0 < f' x then A x else 0)
  rw [hx]

end Yau.F04Proof

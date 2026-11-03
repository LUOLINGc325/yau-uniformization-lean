import Yau.Proofs.F04SupportedIdeality
import Yau.Proofs.F04AmbientPositivePart
import Yau.Proofs.F04EnergyRestriction
import Yau.Proofs.F04PositiveProjection

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03 Yau.LeafProofs.L19Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- The genuine supported ambient-shift test, constructed by proved ideality. -/
def dirichletAmbientShiftPosPart
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (u : DirichletEnergy g μ hμ O) (q : ScalarEnergySpace g μ hμ)
    (hq : ∀ᵐ x ∂μ, 0 ≤ scalarEnergyL2 g μ hμ q x) : DirichletEnergy g μ hμ O :=
  Classical.choose (dirichletEnergy_ambient_shift_posPart g hK μ hμ O hO u q hq)

theorem dirichletAmbientShiftPosPart_ambient_L2
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (u : DirichletEnergy g μ hμ O) (q : ScalarEnergySpace g μ hμ)
    (hq : ∀ᵐ x ∂μ, 0 ≤ scalarEnergyL2 g μ hμ q x) :
    scalarEnergyL2 g μ hμ (dirichletAmbientShiftPosPart g hK μ hμ O hO u q hq).val =
      Lp.posPart (scalarEnergyL2 g μ hμ u.val - scalarEnergyL2 g μ hμ q) :=
  (Classical.choose_spec (dirichletEnergy_ambient_shift_posPart g hK μ hμ O hO u q hq)).1

theorem dirichletAmbientShiftPosPart_L2
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (u : DirichletEnergy g μ hμ O) (q : ScalarEnergySpace g μ hμ)
    (hq : ∀ᵐ x ∂μ, 0 ≤ scalarEnergyL2 g μ hμ q x) :
    dirichletL2 g μ hμ O (dirichletAmbientShiftPosPart g hK μ hμ O hO u q hq) =
      Lp.posPart (dirichletL2 g μ hμ O u - l2Restriction μ O (scalarEnergyL2 g μ hμ q)) := by
  change l2Restriction μ O (scalarEnergyL2 g μ hμ
    (dirichletAmbientShiftPosPart g hK μ hμ O hO u q hq).val) = _
  rw [dirichletAmbientShiftPosPart_ambient_L2, l2Restriction_posPart, map_sub]
  rfl

/-- The rough ambient shift has the actual strict-active differential in the
supported form space, obtained by restricting its proved ambient chain rule. -/
theorem dirichletAmbientShiftPosPart_D
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (u : DirichletEnergy g μ hμ O) (q : ScalarEnergySpace g μ hμ)
    (hq : ∀ᵐ x ∂μ, 0 ≤ scalarEnergyL2 g μ hμ q x) :
    dirichletD g μ hμ O (dirichletAmbientShiftPosPart g hK μ hμ O hO u q hq) =
      positiveFormMultiplier g (μ.restrict O)
        (dirichletL2 g μ hμ O u - l2Restriction μ O (scalarEnergyL2 g μ hμ q))
        (dirichletD g μ hμ O u - scalarEnergyD g μ hμ O q) := by
  let v := dirichletAmbientShiftPosPart g hK μ hμ O hO u q hq
  let d := u.val - q
  let f := dirichletL2 g μ hμ Set.univ (scalarEnergyUnivEquiv g μ hμ d)
  let f' := l2Restriction μ O (scalarEnergyL2 g μ hμ d)
  let R := formMeasureRestriction (k := 1) g (μ.restrict Set.univ) (μ.restrict O)
    (by simpa only [Measure.restrict_univ] using Measure.restrict_le_self)
  have hglobal : scalarEnergyL2 g μ hμ v.val = Lp.posPart (scalarEnergyL2 g μ hμ d) := by
    simpa only [d, map_sub] using dirichletAmbientShiftPosPart_ambient_L2 g hK μ hμ O hO u q hq
  have hf : f' =ᵐ[μ.restrict O] f := by
    filter_upwards [restrictL2_coe μ O (scalarEnergyL2 g μ hμ d),
      ae_restrict_of_ae (dirichletL2_univ_ae g μ hμ d)] with x hr hu
    exact hr.trans hu.symm
  have hd := scalarEnergyD_positive_of_ambient_eq g hK μ hμ v.val d hglobal
  have hrestrict := congrArg R hd
  rw [scalarEnergyD_restrict_univ,
    formMeasureRestriction_positive g _ _ _ f f' hf,
    scalarEnergyD_restrict_univ] at hrestrict
  change scalarEnergyD g μ hμ O v.val = _
  have huJ : l2Restriction μ O (scalarEnergyL2 g μ hμ u.val) = dirichletL2 g μ hμ O u := rfl
  have huD : scalarEnergyD g μ hμ O u.val = dirichletD g μ hμ O u := rfl
  simpa only [d, f', map_sub, huJ, huD] using hrestrict

end Yau.F04Proof

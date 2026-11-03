import Yau.Proofs.F04InclusionValues
import Yau.Proofs.F04ShiftPositiveDifferential
import Yau.Proofs.F04SmoothCompositionCore

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.HeatConcreteBindings

variable {n : ℕ} {M : ComplexManifold n}

/-- The genuine smooth shifted test on the small domain is the positive
 part of the actual included difference on the larger domain. -/
theorem dirichletInclusion_shiftPosPart
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {O W : Set M.Carrier}
    (hO : IsOpen O) (hW : IsOpen W) (hOW : O ⊆ W)
    (r : M.Carrier → ℝ) (hr : SmoothFn r) (hr0 : ∀ x ∈ O, 0 ≤ r x)
    (hr2 : ScalarL2 (μ.restrict O) r)
    (hdr2 : L2RealForm g.form (μ.restrict O) (scalarExterior r))
    (f : dirichletCore g μ hμ W) (hf0 : ∀ x ∈ W, 0 ≤ f.val x)
    (hfr : ∀ x ∈ O, f.val x = r x) (u : DirichletEnergy g μ hμ O) :
    dirichletInclusion g μ hμ hOW
      (dirichletShiftPosPart g μ hμ O hO r hr hr0 hr2 hdr2 u) =
      dirichletPosPart g μ hμ W hW.measurableSet
        (dirichletInclusion g μ hμ hOW u - dirichletCoreToEnergy g μ hμ W f) := by
  let I := dirichletInclusion g μ hμ hOW
  let j := dirichletL2 g μ hμ O
  let J := dirichletL2 g μ hμ W
  let w := dirichletShiftPosPart g μ hμ O hO r hr hr0 hr2 hdr2 u
  let q := dirichletCoreToEnergy g μ hμ W f
  have hw : (j w : M.Carrier → ℝ) =ᵐ[μ.restrict O] (fun x => max (j u x - r x) 0) := by
    have hj := (dirichletShiftPosPart_spec g μ hμ O hO r hr hr0 hr2 hdr2 u).1
    change j w = Lp.posPart (j u - scalarToLp hr2) at hj
    rw [hj]
    filter_upwards [Lp.coeFn_posPart (j u - scalarToLp hr2), Lp.coeFn_sub (j u) (scalarToLp hr2),
      scalarToLp_coe hr2] with x hp hs hrx
    rw [hp, hs, Pi.sub_apply, hrx]
  have hLift : O.indicator (j w) =ᵐ[μ] O.indicator (fun x => max (j u x - r x) 0) :=
    (ae_eq_restrict_iff_indicator_ae_eq hO.measurableSet).mp hw
  apply dirichletL2_injective g hK μ hμ W hW.measurableSet
  rw [(dirichletPosPart_spec g μ hμ W hW.measurableSet (I u - q)).1, map_sub]
  apply Lp.ext
  filter_upwards [dirichletInclusion_L2_ae g μ hμ hO.measurableSet hW.measurableSet hOW w,
    dirichletInclusion_L2_ae g μ hμ hO.measurableSet hW.measurableSet hOW u,
    ae_restrict_of_ae hLift, dirichletCoreL2_ae g μ hμ W f,
    Lp.coeFn_posPart (J (I u) - J q), Lp.coeFn_sub (J (I u)) (J q),
    ae_restrict_mem hW.measurableSet] with x hwx hux hLiftx hfx hp hs hxW
  change J (I w) x = _
  change J (I w) x = O.indicator (j w) x at hwx
  change J (I u) x = O.indicator (j u) x at hux
  change J q x = f.val x at hfx
  rw [hwx, hp, hs, Pi.sub_apply, hux, hfx, hLiftx]
  by_cases hxO : x ∈ O
  · simp only [indicator_of_mem hxO, hfr x hxO]
  · simp only [indicator_of_notMem hxO, zero_sub]
    exact (max_eq_right (neg_nonpos.mpr (hf0 x hxW))).symm

end Yau.F04Proof

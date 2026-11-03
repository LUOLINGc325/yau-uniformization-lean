import Yau.Proofs.F04PositiveContinuity
import Yau.Proofs.F04PositiveEnergyHilbert
import Yau.LeafProofs.L16LionsTimeTrace

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L16HilbertTimeRegularization

variable {n : ℕ} {M : ComplexManifold n}

/-- Differentiate the C1 convex scalar functional on the L2 pivot, along a
smooth actual V curve. The positive-part V curve is never differentiated. -/
theorem dirichlet_hasDerivAt_positiveEnergy
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : MeasurableSet O)
    {z : ℝ → DirichletEnergy g μ hμ O} (hz : ContDiff ℝ 1 z)
    {Q : ℝ → StrongDual ℝ (DirichletEnergy g μ hμ O)} (t : ℝ)
    (hQ : hilbertEmbedding (dirichletL2 g μ hμ O) (deriv z t) = Q t) :
    HasDerivAt (fun r => positiveEnergy (dirichletL2 g μ hμ O (z r)))
      (Q t (dirichletPosPart g μ hμ O hO (z t))) t := by
  let J := dirichletL2 g μ hμ O
  have hd : HasDerivAt z (deriv z t) t :=
    (hz.differentiable (by simp)).differentiableAt.hasDerivAt
  have hh := (positiveEnergy_hasFDerivAt (J (z t))).comp_hasDerivAt t
    (J.hasFDerivAt.comp_hasDerivAt t hd)
  have he : Q t (dirichletPosPart g μ hμ O hO (z t)) =
      inner ℝ (Lp.posPart (J (z t))) (J (deriv z t)) := by
    rw [← hQ, hilbertEmbedding_apply, (dirichletPosPart_spec g μ hμ O hO (z t)).1,
      real_inner_comm]
  change HasDerivAt (fun r => positiveEnergy (J (z r)))
    (inner ℝ (Lp.posPart (J (z t))) (J (deriv z t))) t at hh
  rw [← he] at hh
  exact hh

theorem smooth_positive_energy_increment
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : MeasurableSet O)
    {T : ℝ} {z : ℝ → DirichletEnergy g μ hμ O} (hz : ContDiff ℝ 1 z)
    {Q : ℝ → StrongDual ℝ (DirichletEnergy g μ hμ O)}
    (hQc : ContinuousOn Q (Icc 0 T))
    (hd : ∀ r ∈ Icc 0 T, hilbertEmbedding (dirichletL2 g μ hμ O) (deriv z r) = Q r)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    ‖Lp.posPart (dirichletL2 g μ hμ O (z t))‖ ^ 2 -
      ‖Lp.posPart (dirichletL2 g μ hμ O (z s))‖ ^ 2 =
      2 * ∫ r in s..t, Q r (dirichletPosPart g μ hμ O hO (z r)) := by
  have hc : ContinuousOn (fun r => Q r (dirichletPosPart g μ hμ O hO (z r))) (Icc 0 T) :=
    hQc.clm_apply (((continuous_dirichletPosPart g hK μ hμ O hO).comp hz.continuous).continuousOn)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r hr => dirichlet_hasDerivAt_positiveEnergy g μ hμ O hO hz r (hd r (uIcc_subset_Icc hs ht hr)))
    (hc.mono (uIcc_subset_Icc hs ht)).intervalIntegrable
  dsimp only [positiveEnergy] at he
  linarith

end Yau.F04Proof

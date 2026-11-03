import Yau.Proofs.F04InclusionValues
import Yau.Proofs.F03ScalarL2Pairing

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.HeatConcreteBindings

variable {n : ℕ} {M : ComplexManifold n}

theorem dirichletInclusion_L2_norm
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {O W : Set M.Carrier} (hO : MeasurableSet O) (hW : MeasurableSet W) (hOW : O ⊆ W)
    (u : DirichletEnergy g μ hμ O) :
    ‖dirichletL2 g μ hμ W (dirichletInclusion g μ hμ hOW u)‖ = ‖dirichletL2 g μ hμ O u‖ := by
  have hn := congrArg norm (dirichletInclusion_L2_zeroExtension g μ hμ hO hW hOW u)
  simpa only [l2ZeroExtension_norm] using hn

theorem dirichletInclusion_L2_pairing
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {O W : Set M.Carrier} (hO : MeasurableSet O) (hW : MeasurableSet W) (hOW : O ⊆ W)
    (f F : M.Carrier → ℝ) (hf : ScalarL2 (μ.restrict O) f) (hF : ScalarL2 (μ.restrict W) F)
    (hEq : F =ᵐ[μ.restrict O] f) (u : DirichletEnergy g μ hμ O) :
    inner ℝ (scalarToLp hF) (dirichletL2 g μ hμ W (dirichletInclusion g μ hμ hOW u)) =
      inner ℝ (scalarToLp hf) (dirichletL2 g μ hμ O u) := by
  have hLift : O.indicator F =ᵐ[μ] O.indicator f :=
    (ae_eq_restrict_iff_indicator_ae_eq hO).mp hEq
  have hLeft : inner ℝ (scalarToLp hF) (dirichletL2 g μ hμ W (dirichletInclusion g μ hμ hOW u)) =
      ∫ x, O.indicator (fun y => f y * dirichletL2 g μ hμ O u y) x ∂μ.restrict W := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [scalarToLp_coe hF, dirichletInclusion_L2_ae g μ hμ hO hW hOW u,
      ae_restrict_of_ae hLift] with x hFx hJx hEx
    simp only [RCLike.inner_apply, conj_trivial, hFx, hJx]
    by_cases hx : x ∈ O
    · simp only [indicator_of_mem hx] at hEx ⊢
      rw [hEx, mul_comm]
    · simp only [indicator_of_notMem hx, zero_mul]
  have hRight : inner ℝ (scalarToLp hf) (dirichletL2 g μ hμ O u) =
      ∫ x, f x * dirichletL2 g μ hμ O u x ∂μ.restrict O := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [scalarToLp_coe hf] with x hx
    simp only [RCLike.inner_apply, conj_trivial, hx, mul_comm]
  rw [hLeft, integral_indicator hO, Measure.restrict_restrict hO, inter_eq_left.mpr hOW, hRight]

end Yau.F04Proof

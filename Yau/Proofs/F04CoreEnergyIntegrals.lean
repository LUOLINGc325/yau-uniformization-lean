import Yau.Proofs.F04DirichletCore

open MeasureTheory Set
open scoped InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L19Aux Yau.LeafProofs.L18Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem dirichletCoreEmbedding_norm_integral (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (f : dirichletCore g μ hμ O) :
    ‖dirichletCoreEmbedding g μ hμ O f‖ ^ 2 =
      (∫ x, f.val x * f.val x ∂μ) + (1 / 2 : ℝ) * ∫ x, scalarGradientPair g.form f.val f.val x ∂μ := by
  rw [dirichletCoreEmbedding_norm, ← real_inner_self_eq_norm_sq, scalarEnergyDomain_inner]
  rfl

theorem dirichletCoreEmbedding_pivot_norm_integral (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (f : dirichletCore g μ hμ O) :
    ‖dirichletL2 g μ hμ O (dirichletCoreEmbedding g μ hμ O f)‖ ^ 2 = ∫ x, f.val x * f.val x ∂μ := by
  change ‖dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O f)‖ ^ 2 = _
  rw [dirichletL2_core, ← real_inner_self_eq_norm_sq, scalarEnergyDomainRestrictedL2_inner]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hz : f.val x = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hx (f.property hs))
  rw [hz, zero_mul]

end Yau.F04Proof

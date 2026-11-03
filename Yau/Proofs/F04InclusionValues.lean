import Yau.Proofs.F04LocalFormInclusion

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem dirichletInclusion_L2_zeroExtension
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {O W : Set M.Carrier} (hO : MeasurableSet O) (hW : MeasurableSet W) (hOW : O ⊆ W)
    (u : DirichletEnergy g μ hμ O) :
    l2ZeroExtension μ W hW (dirichletL2 g μ hμ W (dirichletInclusion g μ hμ hOW u)) =
      l2ZeroExtension μ O hO (dirichletL2 g μ hμ O u) := by
  rw [dirichletL2_zeroExtension g μ hμ W hW, dirichletL2_zeroExtension g μ hμ O hO,
    dirichletInclusion_val]

/-- Inclusion has its literal zero-extended scalar values on the larger
 domain, including its actual zero values outside the smaller domain. -/
theorem dirichletInclusion_L2_ae
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {O W : Set M.Carrier} (hO : MeasurableSet O) (hW : MeasurableSet W) (hOW : O ⊆ W)
    (u : DirichletEnergy g μ hμ O) :
    (dirichletL2 g μ hμ W (dirichletInclusion g μ hμ hOW u) : M.Carrier → ℝ) =ᵐ[μ.restrict W]
      O.indicator (dirichletL2 g μ hμ O u) := by
  have hExt : extendL2 μ W hW (dirichletL2 g μ hμ W (dirichletInclusion g μ hμ hOW u)) =
      extendL2 μ O hO (dirichletL2 g μ hμ O u) :=
    dirichletInclusion_L2_zeroExtension g μ hμ hO hW hOW u
  have hBig := extendL2_coe μ W hW (dirichletL2 g μ hμ W (dirichletInclusion g μ hμ hOW u))
  have hSmall := extendL2_coe μ O hO (dirichletL2 g μ hμ O u)
  rw [hExt] at hBig
  filter_upwards [ae_restrict_of_ae hBig, ae_restrict_of_ae hSmall, ae_restrict_mem hW] with x hb hs hx
  rw [indicator_of_mem hx] at hb
  exact hb.symm.trans hs

end Yau.F04Proof

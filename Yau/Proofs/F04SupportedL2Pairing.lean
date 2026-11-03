import Yau.Proofs.F03DirichletEnergy

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace
noncomputable section
namespace Yau.F04Proof
open Yau.Proofs.F03Aux Yau.LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem l2ZeroExtension_inner
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (Ω : Set α) (hΩ : MeasurableSet Ω)
    (f k : Lp ℝ 2 (μ.restrict Ω)) :
    inner ℝ (l2ZeroExtension μ Ω hΩ f) (l2ZeroExtension μ Ω hΩ k) = inner ℝ f k :=
  ((LinearMap.norm_map_iff_inner_map_map (𝕜 := ℝ) (l2ZeroExtension μ Ω hΩ)).mp
    (l2ZeroExtension_norm μ Ω hΩ)) f k

/-- A supported pivot paired with a genuine compact energy test is exactly
 its actual zero extension paired with that test in the original global
 scalar L2 space. This holds for arbitrary actual pivot vectors. -/
theorem supportedL2_core_pairing
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω)
    (f : Lp ℝ 2 (μ.restrict Ω)) (k : dirichletCore g μ hμ Ω) :
    inner ℝ f (dirichletL2 g μ hμ Ω (dirichletCoreToEnergy g μ hμ Ω k)) =
      inner ℝ (l2ZeroExtension μ Ω hΩ f) (scalarEnergyDomainL2 g μ hμ k.val) := by
  rw [← l2ZeroExtension_inner μ Ω hΩ f
    (dirichletL2 g μ hμ Ω (dirichletCoreToEnergy g μ hμ Ω k)),
    dirichletL2_zeroExtension]
  change inner ℝ (l2ZeroExtension μ Ω hΩ f)
    (scalarEnergyL2 g μ hμ (k.val : ScalarEnergySpace g μ hμ)) = _
  rw [scalarEnergyL2_coe]

end Yau.F04Proof

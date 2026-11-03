import Yau.Proofs.V03JointCotangentDifferential

/-! Every genuine smooth intrinsic coefficient has a smooth pullback
along the actual cotangent holomorphic family, on its original parameter set. -/

open scoped Manifold Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem cotangentHolomorphicOn_coefficient_contDiffOn {n : ℕ} {M : ComplexManifold n}
    {P A : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    {S : Set P} {f : P → CotangentPoint M} (hf : CotangentHolomorphicOn f S)
    {b : CotangentPoint M → A}
    (hb : ∀ x, ContDiffOn ℝ ∞ (fun z => b (cotangentChartInv x z)) (cotangentTarget x)) :
    ContDiffOn ℝ ∞ (fun p => b (f p)) S := by
  intro p hp
  obtain ⟨V, hV, hpV, hsource, hcoord⟩ := hf.2 p hp
  have hmodel := (hb (f p).1).comp (hcoord.restrict_scalars ℝ)
    (fun r hr => cotangentChart_mapsTo (f p).1 (hsource r hr))
  apply (contDiffWithinAt_inter (hV.mem_nhds hpV)).mp
  apply (hmodel p ⟨hp, hpV⟩).congr_of_eventuallyEq_of_mem ?_ ⟨hp, hpV⟩
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact congrArg b (cotangentChart_left_inv (f p).1 (hsource r hr)).symm

end Yau.Blueprint.V03Proof

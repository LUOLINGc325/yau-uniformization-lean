import Yau.Proofs.V03FixedGaussTwoFormSmooth

/-! Smoothness of the intrinsic joint Gauss two-form in the actual
induced atlas, with no common chart or extension assumption. -/

open scoped Manifold Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {M : ComplexManifold n}
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]

theorem jointGaussTwoForm_contDiffOn {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) {f : P → CotangentPoint M} {S : Set P}
    (hf : CotangentHolomorphicOn f S) (hS : UniqueDiffOn ℂ S) :
    ContDiffOn ℝ ∞ (jointGaussTwoForm G f S) S := by
  intro p hp
  obtain ⟨V, hV, hpV, hsource, hcoord⟩ := hf.2 p hp
  have hu : UniqueDiffOn ℂ (S ∩ V) :=
    fun r hr => (hS r hr.1).inter (hV.mem_nhds hr.2)
  have hmodel := fixedGaussTwoForm_contDiffOn hG (f p).1 hu hcoord
    (fun r hr => cotangentChart_mapsTo (f p).1 (hsource r hr))
  apply (contDiffWithinAt_inter (hV.mem_nhds hpV)).mp
  apply (hmodel p ⟨hp, hpV⟩).congr_of_eventuallyEq_of_mem ?_ ⟨hp, hpV⟩
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [jointGaussTwoForm_eq_fixed_chart hG hf hr.1 (hS r hr.1) (f p).1 (hsource r hr),
    fderivWithin_inter (hV.mem_nhds hr.2)]

end Yau.Blueprint.V03Proof

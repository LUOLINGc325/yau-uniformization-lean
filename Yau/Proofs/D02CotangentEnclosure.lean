import Yau.Proofs.D02Coercivity
import Yau.Proofs.D02DiscEvaluation

/-! The entire cotangent family is bounded using the same finite spanning fields.
The base enclosure is the preceding base-disc conclusion in the source proof. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n m : ℕ} {M : ComplexManifold n}

/-- A compact in the actual cotangent atlas bounds every fixed scalar evaluation. -/
theorem fieldEvaluation_bound_on_compact {L : Set (CotangentPoint M)}
    (hL : CotangentCompact L) {V : VectorField M} (hV : IsHolomorphicField V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ L, ‖fieldEvaluation V y‖ ≤ C := by
  obtain ⟨C, hC⟩ := (cotangentCompact_image hL
    (fieldEvaluation_continuousOn_chart hV)).bddAbove_image continuous_norm.continuousOn
  refine ⟨max C 0, le_max_right C 0, fun y hy => ?_⟩
  exact (hC (Set.mem_image_of_mem norm (Set.mem_image_of_mem (fieldEvaluation V) hy))).trans
    (le_max_left C 0)

/-- The exact third conclusion follows from the base family enclosure and original spanning fields.
All compact sets and constants are chosen before the varying disc. -/
theorem cotangentFamilyEnclosure_of_baseFamilyEnclosure
    (g : HermitianField M) (hg : MetricSmooth g) {K : Set M.Carrier} (hK : IsCompact K)
    (A₀ R : ℝ) {V : Fin m → VectorField M} (hV : ∀ i, IsHolomorphicField (V i))
    (hspan : ∀ x, Submodule.span ℂ (Set.range fun i => V i x) = ⊤)
    (hbase : ∃ K' : Set M.Carrier, IsCompact K' ∧ ∀ f : ℂ → M.Carrier,
      IsHolomorphicDisc f → (∀ ζ : ℂ, ‖ζ‖ = 1 → f ζ ∈ K) →
      discArea g f ≤ ENNReal.ofReal A₀ → ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → f ζ ∈ K') :
    ∃ K' : Set M.Carrier, ∃ R' : ℝ, IsCompact K' ∧ ∀ (f : ℂ → M.Carrier)
      (ξ : ℂ → Covector n), IsCotangentDisc f ξ →
      (∀ ζ : ℂ, ‖ζ‖ = 1 → InCotangentCompact g K R (f ζ) (ξ ζ)) →
      discArea g f ≤ ENNReal.ofReal A₀ →
      ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → InCotangentCompact g K' R' (f ζ) (ξ ζ) := by
  classical
  have hbox := cotangentBoxCompact n M g hg K R hK
  choose C hCpos hC using fun i => fieldEvaluation_bound_on_compact hbox (hV i)
  obtain ⟨K', hK', hbase⟩ := hbase
  obtain ⟨c, hc, hcoercive⟩ := fieldEvaluationSq_coercive g hg hK' hV hspan
  let B : ℝ := ∑ i, C i ^ 2
  refine ⟨K', B / c, hK', fun f ξ hf hboundary harea ζ hζ => ?_⟩
  have hbaseK : f ζ ∈ K' := hbase f hf.1 (fun w hw => (hboundary w hw).1) harea ζ hζ
  refine ⟨hbaseK, ?_⟩
  have heval (i : Fin m) : ‖fieldEvaluation (V i) (f ζ, ξ ζ)‖ ≤ C i := by
    apply cotangentDisc_fieldEvaluation_norm_le (f := fun z => (f z, ξ z)) hf (hV i) ?_ ζ hζ
    intro w hw
    exact hC i (f w, ξ w) (hboundary w hw)
  have hsum : fieldEvaluationSq V (f ζ, ξ ζ) ≤ B := by
    apply Finset.sum_le_sum
    intro i _
    nlinarith [heval i, hCpos i, norm_nonneg (fieldEvaluation (V i) (f ζ, ξ ζ))]
  apply (le_div_iff₀ hc).mpr
  simpa only [mul_comm] using (hcoercive (f ζ) hbaseK (ξ ζ)).trans hsum

end Yau.NodeProofs.D02Aux

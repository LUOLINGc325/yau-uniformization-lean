import Yau.Proofs.F03InitialSpatialWordBounds
import Yau.Proofs.F03BoundedInitialFaceProducer

/-! The original bounded scalar heat class supplies compact spatial derivative bounds on the closed initial slab. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau Blueprint
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem boundedScalarHeat_compact_spatial_word_bound
    (g : HermitianField M) (f : M.Carrier → ℝ) (u : ℝ → M.Carrier → ℝ)
    (hf : SmoothFn f) (hu : IsBoundedScalarHeat g f u)
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K) (hKt : K ⊆ chartTarget a)
    (R : ℝ) (w : List (ComplexVector n)) :
    ∃ C : ℝ,0 < C ∧ ∀ t ∈ Icc 0 R,∀ z ∈ K,
      |directionalWordDerivative (inChart a (u t)) w z| ≤ C := by
  exact compact_spatial_word_bound_through_initial
    (fun p : ComplexVector n × ℝ => u p.2 (chartInv a p.1)) (inChart a f)
    (isOpen_extChartAt_target (I := ComplexModel n) a) (hu.1 a) (hf a)
    (fun z => congrFun hu.2.1.1 (chartInv a z))
    (fun K hK hKt m ε hε => hu.2.1.2 a K hK hKt m ε hε) K hK hKt R w

theorem boundedScalarHeat_compact_spatial_tensor_bound
    (g : HermitianField M) (f : M.Carrier → ℝ) (u : ℝ → M.Carrier → ℝ)
    (hf : SmoothFn f) (hu : IsBoundedScalarHeat g f u)
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K) (hKt : K ⊆ chartTarget a)
    (R : ℝ) (m : ℕ) :
    ∃ C : ℝ,∀ t ∈ Icc 0 R,∀ z ∈ K,‖iteratedFDeriv ℝ m (inChart a (u t)) z‖ ≤ C := by
  have hOpen := isOpen_extChartAt_target (I := ComplexModel n) a
  have hSlice (t : Icc (0:ℝ) R) : ContDiffOn ℝ ∞ (inChart a (u t.val)) (chartTarget a) := by
    rcases eq_or_lt_of_le t.property.1 with ht0|ht0
    · have he : u t.val=f := by simpa only [← ht0] using hu.2.1.1
      rw [he]
      exact hf a
    · exact (hu.1 a).comp (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz,ht0⟩)
  have hWords (w : List (ComplexVector n)) :
      ∃ C : ℝ,∀ t : Icc (0:ℝ) R,∀ z ∈ K,|directionalWordDerivative (inChart a (u t.val)) w z| ≤ C := by
    obtain ⟨C,_hC,hBound⟩ := boundedScalarHeat_compact_spatial_word_bound g f u hf hu a K hK hKt R w
    exact ⟨C,fun t => hBound t.val t.property⟩
  obtain ⟨C,hC⟩ := iteratedFDeriv_uniform_bound_of_words hOpen hKt
    (fun t : Icc (0:ℝ) R => inChart a (u t.val)) hSlice hWords m
  exact ⟨C,fun t ht => hC ⟨t,ht⟩⟩

end Yau.Proofs.F03Aux

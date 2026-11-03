import Yau.LeafProofs.L22LeviCalculus
import Yau.Proofs.P03Cutoffs

open scoped Topology ContDiff

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.LeafProofs.L22Aux

/-- Finite sums of actual smooth functions preserve the original chartwise
smoothness predicate. -/
theorem smoothFn_finset_sum {n : ℕ} {M : ComplexManifold n} {ι : Type*}
    (s : Finset ι) (F : ι → M.Carrier → ℝ) (hF : ∀ i ∈ s, SmoothFn (F i)) :
    SmoothFn (fun x => ∑ i ∈ s, F i x) := by
  intro a
  change ContDiffOn ℝ ∞ (fun z => ∑ i ∈ s, inChart a (F i) z) (chartTarget a)
  exact ContDiffOn.sum (fun i hi => hF i hi a)

/-- The computed Levi quadratic commutes with finite smooth sums. -/
theorem complexLeviQuadratic_finset_sum {n : ℕ} {ι : Type*}
    (s : Finset ι) (F : ι → ComplexVector n → ℝ) (z v : ComplexVector n)
    (hF : ∀ i ∈ s, ContDiffAt ℝ 2 (F i) z) :
    complexLeviQuadratic (fun x => ∑ i ∈ s, F i x) z v =
      ∑ i ∈ s, complexLeviQuadratic (F i) z v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, complexLeviQuadratic_zero]
  | @insert i s hi ih =>
    have hFs : ∀ j ∈ s, ContDiffAt ℝ 2 (F j) z :=
      fun j hj => hF j (Finset.mem_insert_of_mem hj)
    have hiF := hF i (Finset.mem_insert_self i s)
    simp only [Finset.sum_insert hi]
    rw [complexLeviQuadratic_add hiF (ContDiffAt.sum hFs), ih hFs]

end Yau.NodeProofs.P03Aux

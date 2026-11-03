import Yau.Proofs.F01SpatialDerivativeWords
import Yau.Proofs.F01SpatialTensorBasisBounds
import Mathlib.Data.List.OfFn

/-! Directional derivative words are evaluations of the actual iterated
Fréchet derivative. Finite native-frame Holder bounds therefore control
the full operator tensor, with one constant before the function realization. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem spatialDerivativeWord_ofFn_eq_iteratedFDeriv
    {f : E × ℝ → F} {S : Set E} {t : ℝ}
    (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ (fun x => f (x, t)) S)
    (k : ℕ) (v : Fin k → E) {x : E} (hx : x ∈ S) :
    spatialDerivativeWord (List.ofFn v) f (x, t) =
      iteratedFDeriv ℝ k (fun z => f (z, t)) x v := by
  induction k generalizing x with
  | zero => simp [spatialDerivativeWord]
  | succ k ih =>
    rw [List.ofFn_succ]
    change fderiv ℝ (fun z => spatialDerivativeWord (List.ofFn (Fin.tail v)) f (z, t)) x (v 0) = _
    have he : (fun z => spatialDerivativeWord (List.ofFn (Fin.tail v)) f (z, t)) =ᶠ[𝓝 x]
        (fun z => iteratedFDeriv ℝ k (fun y => f (y, t)) z (Fin.tail v)) := by
      filter_upwards [hS.mem_nhds hx] with z hz
      exact ih (Fin.tail v) hz
    rw [he.fderiv_eq]
    have hiter : DifferentiableAt ℝ (iteratedFDeriv ℝ k (fun z => f (z, t))) x :=
      (hf.contDiffAt (hS.mem_nhds hx)).differentiableAt_iteratedFDeriv
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)
    exact hiter.iteratedFDeriv_succ_apply_left'.symm

open Yau Yau.Parabolic
variable {n : ℕ}

theorem spatial_words_tensor_holder_budget (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : Set (Point n)) (S : Set (Space n)) (β B : ℝ),
      IsOpen S → 0 ≤ B → Q ⊆ S ×ˢ (Set.univ : Set ℝ) →
      ∀ f : Point n → ℝ,
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => f (z, p.2)) S) →
      (∀ m : Fin k → RIdx n,
        HolderBound β Q (spatialDerivativeWord (List.ofFn (fun i => realVec (m i))) f) B) →
      HolderBound β Q (fun p => iteratedFDeriv ℝ k (fun z => f (z, p.2)) p.1) (C * B) := by
  obtain ⟨C, hC, hc⟩ := spatial_tensor_basis_holder_budget (n := n) k
  refine ⟨C, hC, ?_⟩
  intro Q S β B hS hB hQS f hf hb
  apply hc Q β B hB
  intro m
  have he : ∀ p ∈ Q,
      iteratedFDeriv ℝ k (fun z => f (z, p.2)) p.1 (fun i => realVec (m i)) =
        spatialDerivativeWord (List.ofFn (fun i => realVec (m i))) f p := by
    intro p hp
    exact (spatialDerivativeWord_ofFn_eq_iteratedFDeriv hS (hf p hp) k _ (hQS hp).1).symm
  refine ⟨(hb m).1, ?_, ?_⟩
  · intro p hp
    change ‖iteratedFDeriv ℝ k (fun z => f (z, p.2)) p.1 (fun i => realVec (m i))‖ ≤ B
    rw [he p hp]
    exact (hb m).2.1 p hp
  · intro p hp q hq
    change ‖iteratedFDeriv ℝ k (fun z => f (z, p.2)) p.1 (fun i => realVec (m i)) -
      iteratedFDeriv ℝ k (fun z => f (z, q.2)) q.1 (fun i => realVec (m i))‖ ≤ _
    rw [he p hp, he q hq]
    exact (hb m).2.2 p hp q hq

end Yau.NodeProofs.F01Aux

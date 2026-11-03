import Yau.Proofs.F01VectorTensorBasisBounds

/-! Native spatial words give Holder control of the actual vector-valued
iterated Fréchet tensor, including Frobenius matrix targets. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ} {G : Type*}
variable [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

theorem spatial_vector_words_tensor_holder_budget (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : Set (Point n)) (S : Set (Space n)) (β B : ℝ),
      IsOpen S → 0 ≤ B → Q ⊆ S ×ˢ (Set.univ : Set ℝ) →
      ∀ f : Point n → G,
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => f (z, p.2)) S) →
      (∀ m : Fin k → RIdx n,
        HolderBound β Q (spatialDerivativeWord (List.ofFn (fun i => realVec (m i))) f) B) →
      HolderBound β Q (fun p => iteratedFDeriv ℝ k (fun z => f (z, p.2)) p.1) (C * B) := by
  obtain ⟨C, hC, hc⟩ := spatial_vector_tensor_holder_budget (n := n) (G := G) k
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

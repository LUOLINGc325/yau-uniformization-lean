import Yau.Proofs.F01FiniteTaylorHolder

/-! Assemble actual spatial tensor jets of a pair without replacing
the native product norm by unchecked componentwise seminorms. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ} {F G : Type*}
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem holderBound_spatial_tensor_pair {Q : Set (Point n)} {S : Set (Space n)}
    {β C D : ℝ} {f : Point n → F} {g : Point n → G} (k : ℕ)
    (hS : IsOpen S) (hQ : Q ⊆ S ×ˢ (Set.univ : Set ℝ))
    (hfs : ∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => f (z, p.2)) S)
    (hgs : ∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => g (z, p.2)) S)
    (hf : HolderBound β Q (fun p => iteratedFDeriv ℝ k (fun z => f (z, p.2)) p.1) C)
    (hg : HolderBound β Q (fun p => iteratedFDeriv ℝ k (fun z => g (z, p.2)) p.1) D) :
    HolderBound β Q (fun p => iteratedFDeriv ℝ k
      (fun z => (f (z, p.2), g (z, p.2))) p.1) (max C D) := by
  have he (p : Point n) (hp : p ∈ Q) :
      iteratedFDeriv ℝ k (fun z => (f (z, p.2), g (z, p.2))) p.1 =
        (iteratedFDeriv ℝ k (fun z => f (z, p.2)) p.1).prod
          (iteratedFDeriv ℝ k (fun z => g (z, p.2)) p.1) :=
    iteratedFDeriv_prodMk ((hfs p hp).contDiffAt (hS.mem_nhds (hQ hp).1))
      ((hgs p hp).contDiffAt (hS.mem_nhds (hQ hp).1)) (by simp)
  refine ⟨hf.1.trans (le_max_left _ _), ?_, ?_⟩
  · intro p hp
    dsimp only
    rw [he p hp, ContinuousMultilinearMap.opNorm_prod]
    exact max_le_max (hf.2.1 p hp) (hg.2.1 p hp)
  · intro p hp q hq
    dsimp only
    rw [he p hp, he q hq]
    have hsub : (iteratedFDeriv ℝ k (fun z => f (z, p.2)) p.1).prod
          (iteratedFDeriv ℝ k (fun z => g (z, p.2)) p.1) -
        (iteratedFDeriv ℝ k (fun z => f (z, q.2)) q.1).prod
          (iteratedFDeriv ℝ k (fun z => g (z, q.2)) q.1) =
        (iteratedFDeriv ℝ k (fun z => f (z, p.2)) p.1 -
          iteratedFDeriv ℝ k (fun z => f (z, q.2)) q.1).prod
        (iteratedFDeriv ℝ k (fun z => g (z, p.2)) p.1 -
          iteratedFDeriv ℝ k (fun z => g (z, q.2)) q.1) := by ext m <;> rfl
    rw [hsub, ContinuousMultilinearMap.opNorm_prod]
    have hw : 0 ≤ holderWeight β p q := by unfold holderWeight; positivity
    exact max_le ((hf.2.2 p hp q hq).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hw))
      ((hg.2.2 p hp q hq).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hw))

end Yau.NodeProofs.F01Aux

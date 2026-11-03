import Mathlib

/-! The finite-sum algebra behind the weighted basic identity. The Green
identity is the sole adjoint hypothesis; no commutation is required here. -/

noncomputable section
namespace Yau.LeafProofs.L21Aux

theorem additive_basic_identity {V : Type*} [AddCommGroup V] (n : ℕ)
    (b : V →+ V →+ ℝ) (hsym : ∀ u v, b u v = b v u)
    (D Ds : Fin n → V →+ V)
    (hadj : ∀ i u v, b u (D i v) = b (Ds i u) v)
    (v : Fin n → V) :
    b (∑ i, Ds i (v i)) (∑ i, Ds i (v i)) +
        (1 / 2 : ℝ) * ∑ i, ∑ j,
          b (D i (v j) - D j (v i)) (D i (v j) - D j (v i)) =
      (∑ i, ∑ j, b (D i (v j)) (D i (v j))) +
        ∑ i, ∑ j, b (v i) (D i (Ds j (v j)) - Ds j (D i (v j))) := by
  let a := ∑ i, ∑ j, b (D i (v j)) (D i (v j))
  let c := ∑ i, ∑ j, b (D i (v j)) (D j (v i))
  have hdiv : b (∑ i, Ds i (v i)) (∑ i, Ds i (v i)) =
      ∑ i, ∑ j, b (v i) (D i (Ds j (v j))) := by
    simp only [map_sum, AddMonoidHom.finsetSum_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact (hadj i (v i) (Ds j (v j))).symm
  have hcross (i j : Fin n) : b (v i) (Ds j (D i (v j))) = b (D i (v j)) (D j (v i)) :=
    (hsym _ _).trans (hadj j (D i (v j)) (v i)).symm
  have hcomm : (∑ i, ∑ j, b (v i) (D i (Ds j (v j)) - Ds j (D i (v j)))) =
      b (∑ i, Ds i (v i)) (∑ i, Ds i (v i)) - c := by
    simp only [map_sub, Finset.sum_sub_distrib]
    rw [← hdiv]
    simp only [hcross, c]
  have hpair (i j : Fin n) :
      b (D i (v j) - D j (v i)) (D i (v j) - D j (v i)) =
        b (D i (v j)) (D i (v j)) - b (D i (v j)) (D j (v i)) -
          b (D j (v i)) (D i (v j)) + b (D j (v i)) (D j (v i)) := by
    simp only [map_sub, AddMonoidHom.sub_apply]
    ring
  have hswap : (∑ i, ∑ j, b (D j (v i)) (D j (v i))) = a := by
    rw [Finset.sum_comm]
  have hcrossSwap : (∑ i, ∑ j, b (D j (v i)) (D i (v j))) = c := by
    dsimp [c]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact hsym _ _
  have hcurl : (∑ i, ∑ j, b (D i (v j) - D j (v i)) (D i (v j) - D j (v i))) =
      2 * a - 2 * c := by
    simp only [hpair, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hswap, hcrossSwap]
    change a - c - c + a = _
    ring
  rw [hcurl, hcomm]
  change _ = a + _
  ring

end Yau.LeafProofs.L21Aux

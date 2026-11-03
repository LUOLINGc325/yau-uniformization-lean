import Yau.Proofs.G04TraceChart

noncomputable section
open scoped Matrix
namespace Yau.NodeProofs.G04Aux
open Yau Yau.LeafProofs L12Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem kahler_three_contraction (G : Matrix (RIdx n) (RIdx n) ℝ) (hG : G.IsSymm)
    (hGJ : ∀ a b, G (jIndex n a) (jIndex n b) = jSign a * jSign b * G a b)
    (T : RIdx n → RIdx n → RIdx n → ℝ)
    (hAlt : ∀ a b c, T a c b = -T a b c)
    (hJ : ∀ a b c, T a (jIndex n b) (jIndex n c) = jSign b * jSign c * T a b c)
    (hcyc : ∀ a b c, T a b c + T b c a + T c a b = 0) (c : RIdx n) :
    -(∑ a, ∑ b, G a b * T a b c) =
      jSign c * ((1 / 2 : ℝ) * ∑ a, ∑ b, G a b * jSign b * T (jIndex n c) a (jIndex n b)) := by
  let S := ∑ a, ∑ b, G a b * T a b c
  let U := ∑ a, ∑ b, G a b * jSign b * jSign c * T a (jIndex n b) (jIndex n c)
  let V := ∑ a, ∑ b, G a b * jSign b * jSign c * T (jIndex n b) (jIndex n c) a
  let W := ∑ a, ∑ b, G a b * jSign b * jSign c * T (jIndex n c) a (jIndex n b)
  have hU : U = S := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [hJ]
    calc
      _ = (jSign b * jSign b) * (jSign c * jSign c) * (G a b * T a b c) := by ring
      _ = _ := by rw [jSign_sq, jSign_sq]; ring
  have hV : V = S := by
    calc
      V = ∑ a, ∑ b, G (jIndex n a) (jIndex n b) * jSign (jIndex n b) * jSign c *
          T (jIndex n (jIndex n b)) (jIndex n c) (jIndex n a) :=
        (L18Aux.sum_jIndex_two (fun a b => G a b * jSign b * jSign c *
          T (jIndex n b) (jIndex n c) a)).symm
      _ = ∑ a, ∑ b, G a b * T b a c := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        rw [hGJ, jSign_jIndex, jIndex_involutive, hJ, hAlt b a c]
        calc
          _ = (jSign a * jSign a) * (jSign b * jSign b) * (jSign c * jSign c) *
              (G a b * T b a c) := by ring
          _ = _ := by rw [jSign_sq, jSign_sq, jSign_sq]; ring
      _ = S := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        rw [hG.apply a b]
  have hc : W + U + V = 0 := by
    dsimp only [W, U, V]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro a _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro b _
    have he := hcyc (jIndex n c) a (jIndex n b)
    linear_combination (G a b * jSign b * jSign c) * he
  rw [hU, hV] at hc
  have hW : W = jSign c * ∑ a, ∑ b, G a b * jSign b * T (jIndex n c) a (jIndex n b) := by
    dsimp only [W]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  change -S = _
  rw [hW] at hc
  linarith

end Yau.NodeProofs.G04Aux

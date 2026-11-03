import Yau.LeafProofs.L21PrincipalSymbol

/-! Finite Hermitian Gram identities, keeping the positive radial term
as its exact squared norm. -/

noncomputable section
namespace Yau.LeafProofs.L21Aux

theorem complex_re_mul_star (z : ℂ) : (z * star z).re = ‖z‖ ^ 2 := by
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.sq_norm, Complex.normSq_apply]
  ring

theorem finite_hermitian_gram {ι τ : Type*} [Fintype ι] [Fintype τ]
    (p : ι → τ → ℂ) (ξ : ι → ℂ) :
    (∑ i, ∑ j, star (ξ i) * (∑ a, p i a * star (p j a)) * ξ j).re =
      ∑ a, ‖∑ i, star (ξ i) * p i a‖ ^ 2 := by
  have hx (a : τ) : (∑ i, ∑ j, star (ξ i) * (p i a * star (p j a)) * ξ j) =
      (∑ i, star (ξ i) * p i a) * star (∑ i, star (ξ i) * p i a) := by
    rw [star_sum]
    simp only [star_mul, star_star]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have he : (∑ i, ∑ j, star (ξ i) * (∑ a, p i a * star (p j a)) * ξ j) =
      ∑ a, (∑ i, star (ξ i) * p i a) * star (∑ i, star (ξ i) * p i a) := by
    calc
      _ = ∑ i, ∑ j, ∑ a, star (ξ i) * (p i a * star (p j a)) * ξ j := by
        simp only [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ i, ∑ a, ∑ j, star (ξ i) * (p i a * star (p j a)) * ξ j := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = ∑ a, ∑ i, ∑ j, star (ξ i) * (p i a * star (p j a)) * ξ j := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun a _ => hx a
  rw [he]
  simp only [Complex.re_sum, complex_re_mul_star]

theorem finite_hermitian_rank_one {ι τ : Type*} [Fintype ι] [Fintype τ]
    (p : ι → τ → ℂ) (r : τ → ℝ) (ξ : ι → ℂ) :
    (∑ i, ∑ j, star (ξ i) *
      (∑ a, ∑ b, p i a * star (p j b) * (r a : ℂ) * (r b : ℂ)) * ξ j).re =
      ‖∑ a, (∑ i, star (ξ i) * p i a) * (r a : ℂ)‖ ^ 2 := by
  let q (i : ι) : ℂ := ∑ a, p i a * (r a : ℂ)
  have hq (i j : ι) : (∑ a, ∑ b, p i a * star (p j b) * (r a : ℂ) * (r b : ℂ)) =
      q i * star (q j) := by
    dsimp only [q]
    rw [star_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  have hGram := finite_hermitian_gram (fun (i : ι) (_ : Unit) => q i) ξ
  simp only [Fintype.sum_unique] at hGram
  simp only [hq]
  rw [hGram]
  apply congrArg (fun z : ℂ => ‖z‖ ^ 2)
  calc
    _ = ∑ i, ∑ a, star (ξ i) * (p i a * (r a : ℂ)) := by
      dsimp only [q]
      simp only [Finset.mul_sum]
    _ = ∑ a, ∑ i, star (ξ i) * (p i a * (r a : ℂ)) := Finset.sum_comm
    _ = _ := by simp only [Finset.sum_mul, mul_assoc]

end Yau.LeafProofs.L21Aux

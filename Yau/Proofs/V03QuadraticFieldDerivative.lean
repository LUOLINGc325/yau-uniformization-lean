import Yau.Proofs.V03QuadraticWithinDerivative

/-! The actual radial derivative of a Hermitian quadratic field splits
into its coefficient differential and its two genuine velocity derivatives. -/

open scoped Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof

theorem fderivWithin_real_quadratic_apply {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    {S : Set E} {x : E} (hS : UniqueDiffWithinAt ℝ S x)
    {A : E → Matrix ι ι ℂ} {V : E → ι → ℂ}
    (hA : ∀ i j, DifferentiableWithinAt ℝ (fun y => A y i j) S x)
    (hV : ∀ i, DifferentiableWithinAt ℝ (fun y => V y i) S x) (v : E) :
    fderivWithin ℝ (fun y => 2 * (star (V y) ⬝ᵥ (A y *ᵥ V y)).re) S x v =
      2 * (∑ i : ι, ∑ j : ι,
        (star (fderivWithin ℝ (fun y : E => V y (i : ι)) S x v) * A x i j * V x j +
          star (V x i) * fderivWithin ℝ (fun y : E => A y (i : ι) (j : ι)) S x v * V x j +
            star (V x i) * A x i j * fderivWithin ℝ (fun y : E => V y (j : ι)) S x v)).re := by
  have hprod (i j : ι) : DifferentiableWithinAt ℝ
      (fun y => star (V y i) * A y i j * V y j) S x := ((hV i).star.mul (hA i j)).mul (hV j)
  have hsum (i : ι) : DifferentiableWithinAt ℝ
      (fun y => ∑ j : ι, star (V y i) * A y i j * V y j) S x :=
    DifferentiableWithinAt.fun_sum (u := Finset.univ) (fun j _ => hprod i j)
  have hQ : DifferentiableWithinAt ℝ
      (fun y => ∑ i : ι, ∑ j : ι, star (V y i) * A y i j * V y j) S x :=
    DifferentiableWithinAt.fun_sum (u := Finset.univ) (fun i _ => hsum i)
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, ← mul_assoc]
  rw [fderivWithin_two_re_apply hS hQ]
  apply congrArg (fun z : ℂ => 2 * z.re)
  rw [fderivWithin_fun_sum hS (fun i _ => hsum i)]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderivWithin_fun_sum hS (fun j _ => hprod i j)]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact fderivWithin_star_mul_mul_apply hS (hV i) (hA i j) (hV j) v

end Yau.Blueprint.V03Proof

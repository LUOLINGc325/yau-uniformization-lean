import Yau.Proofs.D06CircleConjugation

/-! Linear Fourier weak calculus and finite Sobolev sums for actual circle
matrix entries in the original bootstrap. -/

noncomputable section
namespace Yau.NodeProofs.D06Aux

@[simp] theorem circleCoeff_zero (n : ℤ) : circleCoeff 0 n = 0 := by
  change ((fourierBasis (T := 2 * Real.pi)).repr 0) n = 0
  rw [map_zero]
  rfl

theorem circleCoeff_neg (f : CircleL2) (n : ℤ) : circleCoeff (-f) n = -circleCoeff f n := by
  change ((fourierBasis (T := 2 * Real.pi)).repr (-f)) n = _
  rw [map_neg]
  rfl

theorem circleSobolev_zero_function (k : ℕ) : CircleSobolev k 0 := by
  simp only [CircleSobolev, circleCoeff_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
  exact summable_zero

theorem circleSobolev_neg {k : ℕ} {f : CircleL2} (hf : CircleSobolev k f) : CircleSobolev k (-f) := by
  simpa only [CircleSobolev, circleCoeff_neg, norm_neg] using hf

theorem circleWeakDerivative_add {f g df dg : CircleL2}
    (hf : CircleWeakDerivative f df) (hg : CircleWeakDerivative g dg) :
    CircleWeakDerivative (f + g) (df + dg) := by
  intro n
  rw [circleCoeff_add, circleCoeff_add, hf n, hg n, mul_add]

theorem circleWeakDerivative_neg {f df : CircleL2} (hf : CircleWeakDerivative f df) :
    CircleWeakDerivative (-f) (-df) := by
  intro n
  rw [circleCoeff_neg, circleCoeff_neg, hf n, mul_neg]

theorem circleWeakDerivative_zero : CircleWeakDerivative 0 0 := by
  intro n
  simp only [circleCoeff_zero, mul_zero]

theorem circleSobolev_finsetSum {ι : Type*} (s : Finset ι) (f : ι → CircleL2) (k : ℕ)
    (hf : ∀ i ∈ s, CircleSobolev k (f i)) : CircleSobolev k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using circleSobolev_zero_function k
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact circleSobolev_add (hf i (Finset.mem_insert_self i s))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem circleWeakDerivative_finsetSum {ι : Type*} (s : Finset ι) (f df : ι → CircleL2)
    (hf : ∀ i ∈ s, CircleWeakDerivative (f i) (df i)) :
    CircleWeakDerivative (∑ i ∈ s, f i) (∑ i ∈ s, df i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using circleWeakDerivative_zero
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact circleWeakDerivative_add (hf i (Finset.mem_insert_self i s))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

end Yau.NodeProofs.D06Aux

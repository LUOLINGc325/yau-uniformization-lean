import Yau.Blueprint.Alignment

/-! Differentiate the actual matrix inverse by differentiating its product with the metric. -/

open scoped Topology Matrix
open Filter

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem matrix_inverse_entry_hasDerivAt (H : ℝ → Herm n) (H' : Herm n) {x : ℝ}
    (hH : ∀ i j, HasDerivAt (fun y => H y i j) (H' i j) x)
    (hK : ∀ i j, DifferentiableAt ℝ (fun y => (H y)⁻¹ i j) x)
    (hdet : ∀ᶠ y in 𝓝 x, IsUnit (H y).det) :
    ∀ i j, HasDerivAt (fun y => (H y)⁻¹ i j) (-((H x)⁻¹ * H' * (H x)⁻¹) i j) x := by
  let K' : Herm n := fun i j => deriv (fun y => (H y)⁻¹ i j) x
  have hKder : ∀ i j, HasDerivAt (fun y => (H y)⁻¹ i j) (K' i j) x :=
    fun i j => (hK i j).hasDerivAt
  have heq : (fun y => (H y)⁻¹ * H y) =ᶠ[𝓝 x] fun _ => (1 : Herm n) := by
    filter_upwards [hdet] with y hy
    exact Matrix.nonsing_inv_mul (H y) hy
  have hproduct : K' * H x + (H x)⁻¹ * H' = 0 := by
    ext i j
    have hprod : HasDerivAt (fun y => ∑ k, (H y)⁻¹ i k * H y k j)
        (∑ k, (K' i k * H x k j + (H x)⁻¹ i k * H' k j)) x := by
      convert HasDerivAt.sum (u := Finset.univ) (fun k _ => (hKder i k).mul (hH k j)) using 1
      funext y
      simp only [Finset.sum_apply, Pi.mul_apply]
    have hscalar : (fun y => ∑ k, (H y)⁻¹ i k * H y k j) =ᶠ[𝓝 x]
        fun _ => (1 : Herm n) i j := by
      filter_upwards [heq] with y hy
      exact congrArg (fun A : Herm n => A i j) hy
    have hzero : HasDerivAt (fun y => ∑ k, (H y)⁻¹ i k * H y k j) 0 x :=
      (hasDerivAt_const x ((1 : Herm n) i j)).congr_of_eventuallyEq hscalar
    have hd := hprod.unique hzero
    simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply, Finset.sum_add_distrib] using hd
  have hright : H x * (H x)⁻¹ = 1 := Matrix.mul_nonsing_inv (H x) hdet.self_of_nhds
  have hm : K' * H x = -((H x)⁻¹ * H') := eq_neg_of_add_eq_zero_left hproduct
  have hformula : K' = -((H x)⁻¹ * H' * (H x)⁻¹) := by
    calc
      K' = K' * (H x * (H x)⁻¹) := by rw [hright, Matrix.mul_one]
      _ = (K' * H x) * (H x)⁻¹ := by rw [Matrix.mul_assoc]
      _ = -((H x)⁻¹ * H') * (H x)⁻¹ := by rw [hm]
      _ = _ := by rw [neg_mul]
  intro i j
  simpa only [hformula, Matrix.neg_apply] using hKder i j

end Yau.Blueprint.Alignment.Y03Proof

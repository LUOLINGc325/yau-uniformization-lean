import Yau.Proofs.C01MovingFrameAlgebra

/-! Actual derivatives of matrix quadratic forms with moving vectors. -/

noncomputable section

open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ}

theorem matrix_quadratic_hasDerivAt
    (K : ℝ → Herm n) (v : ℝ → Fin n → ℂ) (D : Herm n) (u : Fin n → ℂ) (t : ℝ)
    (hK : ∀ i j, HasDerivAt (fun s => K s i j) (D i j) t)
    (hv : ∀ i, HasDerivAt (fun s => v s i) (u i) t) :
    HasDerivAt (fun s => star (v s) ⬝ᵥ (K s *ᵥ v s))
      (star u ⬝ᵥ (K t *ᵥ v t) + star (v t) ⬝ᵥ (D *ᵥ v t) +
        star (v t) ⬝ᵥ (K t *ᵥ u)) t := by
  have hi (i : Fin n) := HasDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => (hK i j).mul (hv j))
  have hs := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (hv i).star.mul (hi i))
  convert! hs using 1
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Pi.mul_apply, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc] <;> ring

theorem matrix_moving_quadratic_hasDerivAt
    (K : ℝ → Herm n) (v : ℝ → Fin n → ℂ) (D M : Herm n) (t : ℝ)
    (hK : ∀ i j, HasDerivAt (fun s => K s i j) (D i j) t)
    (hv : ∀ i, HasDerivAt (fun s => v s i) ((M *ᵥ v t) i) t) :
    HasDerivAt (fun s => star (v s) ⬝ᵥ (K s *ᵥ v s))
      (star (v t) ⬝ᵥ ((Mᴴ * K t + D + K t * M) *ᵥ v t)) t := by
  have hl : star (M *ᵥ v t) ⬝ᵥ (K t *ᵥ v t) =
      star (v t) ⬝ᵥ ((Mᴴ * K t) *ᵥ v t) := by
    simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  have hr : star (v t) ⬝ᵥ (K t *ᵥ (M *ᵥ v t)) =
      star (v t) ⬝ᵥ ((K t * M) *ᵥ v t) := by
    rw [Matrix.mulVec_mulVec]
  have hd := matrix_quadratic_hasDerivAt K v D (M *ᵥ v t) t hK hv
  rw [hl, hr] at hd
  simpa only [Matrix.add_mulVec, dotProduct_add] using hd

theorem moving_metric_quadratic_hasDerivAt_zero
    (H : ℝ → Herm n) (v : ℝ → Fin n → ℂ) (A : Herm n) (t : ℝ)
    (hH : (H t).PosDef) (hA : A.IsHermitian)
    (hmetric : ∀ i j, HasDerivAt (fun s => H s i j) (-A i j) t)
    (hframe : ∀ i, HasDerivAt (fun s => v s i)
      ((((1 / 2 : ℂ) • ((H t)⁻¹ * A)) *ᵥ v t) i) t) :
    HasDerivAt (fun s => star (v s) ⬝ᵥ (H s *ᵥ v s)) 0 t := by
  have hd := matrix_moving_quadratic_hasDerivAt H v (-A)
    ((1 / 2 : ℂ) • ((H t)⁻¹ * A)) t hmetric hframe
  rw [moving_frame_metric_cancellation (H t) A hH hA] at hd
  simpa only [Matrix.zero_mulVec, dotProduct_zero] using hd

end Yau.NodeProofs.C01Aux

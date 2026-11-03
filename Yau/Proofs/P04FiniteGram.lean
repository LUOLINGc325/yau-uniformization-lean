import Yau.Proofs.P04RankOneBound

noncomputable section
open scoped Topology InnerProductSpace Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau
variable {n m : ℕ}

def gramFunctional (f : ComplexVector m) (B : Matrix (Fin m) (Fin n) ℂ) (i : Fin n) : ℂ :=
  ∑ k, star (f k)*B k i

def functionalGram (f : ComplexVector m) (B : Matrix (Fin m) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := fun i j => star (gramFunctional f B i)*gramFunctional f B j

theorem gram_conjugate_rankOne (f : ComplexVector m) (B : Matrix (Fin m) (Fin n) ℂ) :
    Bᴴ*radialRankOne f*B = functionalGram f B := by
  let C : Matrix (Fin 1) (Fin m) ℂ := fun _ k => star (f k)
  have hR : radialRankOne f=Cᴴ*C := by
    ext i j
    change f i*star (f j) = ∑ k : Fin 1, star (C k i)*C k j
    simp [C]
  calc
    _ = (C*B)ᴴ*(C*B) := by rw [hR]; simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = _ := by
      ext i j
      change (∑ k : Fin 1, star ((C*B) k i)*(C*B) k j) = _
      simp only [Fintype.sum_unique]
      rfl

/-- Finite Cauchy--Schwarz yields the matrix numerator without division
by the finite sum, including its entire zero set and m=0. -/
theorem finite_gram_numerator_posSemidef (f : ComplexVector m) (B : Matrix (Fin m) (Fin n) ℂ) :
    (((‖f‖^2 : ℝ) : ℂ) • (Bᴴ*B)-
      functionalGram f B).PosSemidef := by
  have H := (radial_cauchy_matrix f).conjTranspose_mul_mul_same B
  rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,
    gram_conjugate_rankOne] at H
  exact H

end Yau.Proofs.P04Aux

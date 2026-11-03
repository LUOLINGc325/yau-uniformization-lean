import Yau.Proofs.F01WirtingerCoordinateChain

/-! Matrix-valued Wirtinger jets are the actual entry derivatives; their
product law uses the original finite matrix multiplication. -/
noncomputable section
open scoped Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs
variable {n : ℕ}

def matrixBarJet (H : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    (z v : ComplexVector n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => wirtBar (fun w => H w i j) z v

def matrixUnbarJet (H : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    (z v : ComplexVector n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => wirt (fun w => H w i j) z v

theorem matrixBarJet_mul
    (A B : ComplexVector n → Matrix (Fin n) (Fin n) ℂ) (z v : ComplexVector n)
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z)
    (hB : ∀ i j, DifferentiableAt ℝ (fun w => B w i j) z) :
    matrixBarJet (fun w => A w * B w) z v = matrixBarJet A z v * B z + A z * matrixBarJet B z v := by
  ext i j
  change wirtBar (fun w => ∑ k, A w i k * B w k j) z v = _
  rw [L14Aux.wirtBar_sum_fun Finset.univ (fun k w => A w i k * B w k j) z v
    (fun k _ => (hA i k).mul (hB k j))]
  simp_rw [L14Aux.wirtBar_mul_rule (fun w => A w i _) (fun w => B w _ j) z v (hA i _) (hB _ j)]
  simp only [matrixBarJet, Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib]

end Yau.NodeProofs.F01Aux

import Yau.Proofs.C05HessianEnergyMatrix
import Yau.Proofs.C05HessianBlocks

/-! In the normalized frame the real trace energy is precisely the sum
of the mixed and pure weighted complex Hessian squares. -/
noncomputable section
open scoped Matrix
namespace Yau.Proofs.C05HessianEnergyAux
open Yau Yau.Proofs.C05Aux
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem inverse_twice_diagonal (w : ι → ℝ) (hw : ∀ i, w i ≠ 0) :
    ((2 : ℝ) • Matrix.diagonal w)⁻¹ =
      (1/2 : ℝ) • Matrix.diagonal (fun i => (w i)⁻¹) := by
  have hD : Matrix.diagonal (fun i => (w i)⁻¹)*Matrix.diagonal w=1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i=j
    · subst j
      simp [hw i]
    · simp [Matrix.diagonal_apply_ne _ hij,Matrix.one_apply_ne hij]
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,hD]
  norm_num

 theorem hessianEnergy_twice_diagonal {n : ℕ} (lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (B : Matrix (RIdx n) (RIdx n) ℝ) :
    hessianEnergy ((2 : ℝ) • 1)
      ((2 : ℝ) • Matrix.diagonal (fun a : RIdx n => lam a.1)) B =
      (1/8 : ℝ)*∑ a : RIdx n, ∑ b : RIdx n, (lam b.1)⁻¹*B a b^2 := by
  have hGI : ((2 : ℝ) • (1 : Matrix (RIdx n) (RIdx n) ℝ))⁻¹ = (1/2 : ℝ) • 1 := by
    simpa using inverse_twice_diagonal (fun _ : RIdx n => (1 : ℝ)) (fun _ => one_ne_zero)
  have hAI := inverse_twice_diagonal (fun a : RIdx n => lam a.1) (fun a => (hlam a.1).ne')
  have ht : (B*Matrix.diagonal (fun a : RIdx n => (lam a.1)⁻¹)*Bᵀ).trace =
      ∑ a : RIdx n, ∑ b : RIdx n, (lam b.1)⁻¹*B a b^2 := by
    change (∑ a : RIdx n, ∑ b : RIdx n,
      (B*Matrix.diagonal (fun a : RIdx n => (lam a.1)⁻¹)) a b * B a b)=_
    simp only [Matrix.mul_diagonal]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  unfold hessianEnergy
  rw [hGI,hAI]
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,Matrix.one_mul,
    Matrix.trace_smul,smul_eq_mul]
  rw [ht]
  ring

 theorem hessianEnergy_diagonal_blocks {n : ℕ} (lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (B : Matrix (RIdx n) (RIdx n) ℝ) (hB : B.IsSymm) :
    hessianEnergy ((2 : ℝ) • 1)
      ((2 : ℝ) • Matrix.diagonal (fun a : RIdx n => lam a.1)) B =
    weightedHessianSquare lam (hessianMixed B)+weightedHessianSquare lam (hessianPure B) := by
  rw [hessianEnergy_twice_diagonal lam hlam B,hessianBlocks_weighted_square]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hB.apply b a]

end Yau.Proofs.C05HessianEnergyAux

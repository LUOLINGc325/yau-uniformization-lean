import Yau.Proofs.P03NakanoLeviAlgebra
import Yau.Proofs.P03GriffithsPullback

open scoped Matrix

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar Yau.LeafProofs

theorem nakano_leviCorrection_eq_columns (L : Matrix (Fin n) (Fin n) ℂ)
    (H : Matrix (Fin r) (Fin r) ℂ) (U : Fin n → Fin r → ℂ) :
    nakanoQuadratic (fun i j => L j i • H) U =
      (∑ α, ∑ β, H α β *
        (∑ i, ∑ j, L i j * star (U i α) * U j β)).re := by
  simp only [nakanoQuadratic, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply congrArg Complex.re
  rw [sum_four_swap]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The base-slot action in the actual Nakano correction is an ordinary
Hermitian congruence, with the original transpose convention preserved. -/
theorem nakano_leviCorrection_base_change (L B : Matrix (Fin n) (Fin n) ℂ)
    (H : Matrix (Fin r) (Fin r) ℂ) (U : Fin n → Fin r → ℂ) :
    nakanoQuadratic (fun i j => L j i • H) (B * Matrix.of U) =
      nakanoQuadratic (fun i j => (Bᴴ * L * B) j i • H) U := by
  calc
    _ = (∑ α, ∑ β, H α β *
        (∑ i, ∑ j, L i j * star ((B * Matrix.of U) i α) * (B * Matrix.of U) j β)).re :=
      nakano_leviCorrection_eq_columns L H (show Fin n → Fin r → ℂ from B * Matrix.of U)
    _ = (∑ α, ∑ β, H α β *
        (∑ i, ∑ j, (Bᴴ * L * B) i j * star (U i α) * U j β)).re := by
      apply congrArg Complex.re
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro β _
      apply congrArg (fun z => H α β * z)
      exact (L07Aux.sesquilinear_matrix_conjugate L B (fun i => U i β) (fun i => U i α)).symm
    _ = _ := (nakano_leviCorrection_eq_columns (Bᴴ * L * B) H U).symm

end Yau.NodeProofs.P03Aux

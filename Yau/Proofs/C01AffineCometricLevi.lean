import Yau.Proofs.C01AffineCotangentJets
import Yau.Proofs.C01CotangentJetAlgebra

/-! The actual Levi derivative of a cometric tested against a freely
chosen affine holomorphic cotangent section. -/

noncomputable section

open scoped Topology ContDiff Matrix

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

theorem affine_cometric_entry_mixed (K : ℂ → ℂ)
    (hK : ContDiffAt ℝ 2 K 0) (c d e f : ℂ) :
    wirt (fun p => wirtBar (fun q : ℂ =>
      (c + q * d) * K q * star (e + q * f)) p 1) 0 1 =
      c * wirt (fun p => wirtBar K p 1) 0 1 * star e +
      d * wirtBar K 0 1 * star e + c * wirt K 0 1 * star f +
      d * K 0 * star f := by
  have hf : ContDiffAt ℝ 2 (fun p : ℂ => c + p * d) 0 := by fun_prop
  have hg : ContDiffAt ℝ 2 (fun p : ℂ => star (e + p * f)) 0 :=
    Complex.conjCLE.contDiff.contDiffAt.comp 0
      (show ContDiffAt ℝ 2 (fun p : ℂ => e + p * f) 0 from by fun_prop)
  rw [wirt_wirtBar_product (hf.mul hK) hg]
  simp only [conjugateAffine_wirt, conjugateAffine_wirtBar,
    conjugateAffine_mixed_wirt, zero_mul, mul_zero, add_zero, zero_add]
  rw [wirt_wirtBar_product hf hK,
    wirt_product (hf.differentiableAt (by norm_num)) (hK.differentiableAt (by norm_num))]
  simp only [affine_mixed_wirt, affine_wirtBar, affine_wirt,
    zero_mul, mul_zero, add_zero, zero_add]
  have hconst (a : ℂ) : wirt (fun _ : ℂ => a) 0 1 = 0 := by simp [wirt]
  simp only [hconst, mul_zero, zero_mul, add_zero, zero_add]
  ring

theorem affine_cometric_quadratic_mixed {n : ℕ}
    (K : ℂ → Herm n) (hK : ∀ i j, ContDiffAt ℝ 2 (fun p => K p i j) 0)
    (ξ ν : Fin n → ℂ) :
    let K₁ : Herm n := fun i j => wirt (fun p => K p i j) 0 1
    let K₂ : Herm n := fun i j => wirtBar (fun p => K p i j) 0 1
    let K₁₂ : Herm n := fun i j => wirt (fun p => wirtBar (fun q => K q i j) p 1) 0 1
    wirt (fun p => wirtBar (fun q : ℂ =>
      ∑ i, ∑ j, (ξ i + q * ν i) * K q i j * star (ξ j + q * ν j)) p 1) 0 1 =
      star (star ξ) ⬝ᵥ (K₁₂ *ᵥ star ξ) +
      star (star ν) ⬝ᵥ (K₂ *ᵥ star ξ) +
      star (star ξ) ⬝ᵥ (K₁ *ᵥ star ν) +
      star (star ν) ⬝ᵥ (K 0 *ᵥ star ν) := by
  dsimp only
  have hterms (i j : Fin n) : ContDiffAt ℝ 2
      (fun p : ℂ => (ξ i + p * ν i) * K p i j * star (ξ j + p * ν j)) 0 := by
    have hleft : ContDiffAt ℝ 2 (fun p : ℂ => ξ i + p * ν i) 0 := by fun_prop
    have hright : ContDiffAt ℝ 2 (fun p : ℂ => star (ξ j + p * ν j)) 0 :=
      Complex.conjCLE.contDiff.contDiffAt.comp 0
        (show ContDiffAt ℝ 2 (fun p : ℂ => ξ j + p * ν j) 0 from by fun_prop)
    exact (hleft.mul (hK i j)).mul hright
  have hrows (i : Fin n) : ContDiffAt ℝ 2
      (fun p : ℂ => ∑ j, (ξ i + p * ν i) * K p i j * star (ξ j + p * ν j)) 0 :=
    ContDiffAt.sum (fun j _ => hterms i j)
  calc
    _ = ∑ i, wirt (fun p => wirtBar
        (fun q : ℂ => ∑ j, (ξ i + q * ν i) * K q i j * star (ξ j + q * ν j)) p 1) 0 1 :=
      wirt_wirtBar_fintype_sum _ 0 1 1 hrows
    _ = ∑ i, ∑ j, wirt (fun p => wirtBar
        (fun q : ℂ => (ξ i + q * ν i) * K q i j * star (ξ j + q * ν j)) p 1) 0 1 := by
      apply Finset.sum_congr rfl
      intro i _
      exact wirt_wirtBar_fintype_sum _ 0 1 1 (hterms i)
    _ = ∑ i, ∑ j,
        (ξ i * wirt (fun p => wirtBar (fun q => K q i j) p 1) 0 1 * star (ξ j) +
        ν i * wirtBar (fun p => K p i j) 0 1 * star (ξ j) +
        ξ i * wirt (fun p => K p i j) 0 1 * star (ν j) +
        ν i * K 0 i j * star (ν j)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact affine_cometric_entry_mixed (fun p => K p i j) (hK i j) (ξ i) (ν i) (ξ j) (ν j)
    _ = _ := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_star,
        Finset.mul_sum, Finset.sum_add_distrib, mul_assoc]

end Yau.NodeProofs.C01Aux

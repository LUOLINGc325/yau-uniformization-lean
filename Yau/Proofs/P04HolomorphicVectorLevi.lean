import Yau.Proofs.P04VectorNormGradient
import Yau.Proofs.P04FiniteGram
import Yau.Proofs.P04LogLeviPositivity
import Yau.LeafProofs.L17RicciNaturality

noncomputable section
open scoped Topology ContDiff Matrix ComplexOrder InnerProductSpace

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs

/-- Full vector-valued Gram identity in the original Levi convention. -/
theorem leviC_vectorNormSq_holomorphic {n m : ℕ}
    {f : ComplexVector n → ComplexVector m} {z : ComplexVector n}
    (hf : ContDiffAt ℂ 2 f z) :
    leviC (fun y => ‖f y‖^2) z =
      (L17Aux.linearMatrix (fderiv ℂ f z))ᴴ*L17Aux.linearMatrix (fderiv ℂ f z) := by
  have hq : ContDiffAt ℝ 2 (poleQuadratic (0 : ComplexVector m) 0) (f z) :=
    (poleQuadratic_smooth _ _).contDiffAt.of_le (by simp)
  have heq : poleQuadratic (0 : ComplexVector m) 0 ∘ f = fun y => ‖f y‖^2 := by
    funext y
    simp [poleQuadratic]
  have H := L17Aux.leviC_comp (f := poleQuadratic (0 : ComplexVector m) 0) hf hq
  rw [heq,leviC_poleQuadratic,Matrix.mul_one] at H
  exact H

theorem gradientGram_vectorNormSq {n m : ℕ}
    {f : ComplexVector n → ComplexVector m} {z : ComplexVector n}
    (hf : DifferentiableAt ℂ f z) :
    gradientGram (fun y => ‖f y‖^2) z =
      functionalGram (f z) (L17Aux.linearMatrix (fderiv ℂ f z)) := by
  have heq (i : Fin n) :
      wirt (fun y => ((‖f y‖^2 : ℝ) : ℂ)) z (stdVec i) =
        gramFunctional (f z) (L17Aux.linearMatrix (fderiv ℂ f z)) i := by
    rw [wirt_vectorNormSq_holomorphic hf]
    simp only [EuclideanSpace.inner_eq_star_dotProduct,gramFunctional,L17Aux.linearMatrix,
      dotProduct,Pi.star_apply]
    apply Finset.sum_congr rfl
    intro k _
    ring
  ext i j
  change star (wirt (fun y => ((‖f y‖^2 : ℝ) : ℂ)) z (stdVec i))*
    wirt (fun y => ((‖f y‖^2 : ℝ) : ℂ)) z (stdVec j) = _
  rw [heq,heq]
  rfl

/-- The numerator stays semipositive at every zero of every finite sum. -/
theorem holomorphic_vectorNormSq_numerator {n m : ℕ}
    {f : ComplexVector n → ComplexVector m} {z : ComplexVector n}
    (hf : ContDiffAt ℂ 2 f z) :
    (((‖f z‖^2 : ℝ) : ℂ) • leviC (fun y => ‖f y‖^2) z-
      gradientGram (fun y => ‖f y‖^2) z).PosSemidef := by
  rw [leviC_vectorNormSq_holomorphic hf,gradientGram_vectorNormSq (hf.differentiableAt (by norm_num))]
  exact finite_gram_numerator_posSemidef _ _

end Yau.Proofs.P04Aux

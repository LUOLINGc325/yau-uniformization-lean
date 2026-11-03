import Yau.Proofs.D06HardyGramFourier
import Yau.Proofs.D06FourierUniqueness

/-! The original normalized weighted Hardy matrix has boundary Gram identity,
and its actual inverse gives the original positive matrix factorization AE. -/

open scoped ComplexOrder Matrix
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}
variable (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
variable (hLp : ∀ i j, MemLp (fun t => L t i j) ⊤ hardyCircleMeasure)
variable (hHerm : ∀ t, (L t).IsHermitian)
variable (m : ℝ) (hm : 0 < m)
variable (hLower : ∀ t, (L t - (m : ℂ) • 1).PosSemidef)
variable (M : ℝ) (hM : 0 ≤ M)
variable (hUpper : ∀ t, ((M : ℂ) • 1 - L t).PosSemidef)

theorem hardyPTrace_gram : ∀ᵐ t ∂hardyCircleMeasure,
    (hardyPTrace L hLp hHerm m hm hLower M hM hUpper t)ᴴ * L t *
      hardyPTrace L hLp hHerm m hm hLower M hM hUpper t = 1 := by
  have hentry (i j : Fin r) :
      hardyWeightedPoint L
        (hardyPColumns L hLp hHerm m hm hLower M hM hUpper i)
        (hardyPColumns L hLp hHerm m hm hLower M hM hUpper j) =ᵐ[hardyCircleMeasure]
      fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) i j := by
    apply hardy_fourierCoeff_unique
    · exact (hardyPGram_memLp_top L hLp hHerm m hm hLower M hM hUpper i j).mono_exponent le_top
    · exact memLp_const _
    · intro n
      rw [hardyPGram_fourier, hardy_fourierCoeff_const]
  have hall : ∀ᵐ t ∂hardyCircleMeasure, ∀ i j,
      hardyWeightedPoint L
        (hardyPColumns L hLp hHerm m hm hLower M hM hUpper i)
        (hardyPColumns L hLp hHerm m hm hLower M hM hUpper j) t =
          (1 : Matrix (Fin r) (Fin r) ℂ) i j :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (hentry i))
  filter_upwards [hall] with t ht
  ext i j
  exact (hardyMatrix_gram_entry L _ t i j).trans (ht i j)

theorem hardyQTrace_factor : ∀ᵐ t ∂hardyCircleMeasure,
    L t = (hardyQTrace L hLp hHerm m hm hLower M hM hUpper t)ᴴ *
      hardyQTrace L hLp hHerm m hm hLower M hM hUpper t := by
  filter_upwards [hardyPTrace_gram L hLp hHerm m hm hLower M hM hUpper,
    hardyPTrace_inverse L hLp hHerm m hm hLower M hM hUpper] with t hg hi
  exact factor_of_normalized_inverse _ _ _ hi.1 hg

end Yau.NodeProofs.D06Aux

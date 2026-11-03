import Yau.Proofs.D06FourierUniqueness

/-! The Hardy product has constant Fourier coefficient equal to the product
of its constant coefficients. This applies before boundary smoothness. -/

open scoped ComplexConjugate
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

theorem hardy_fourierCoeff_conj (f : HardyCircle → ℂ) (n : ℤ) :
    fourierCoeff (fun t => conj (f t)) n = conj (fourierCoeff f (-n)) := by
  unfold fourierCoeff
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  simp only [neg_neg, smul_eq_mul, map_mul, ← fourier_neg]

theorem hardyTrace_star_fourier (a : HardySeq r) (i : Fin r) (n : ℤ) :
    fourierCoeff (star (hardyTraceLp a i) : Lp ℂ 2 hardyCircleMeasure) n =
      conj (if 0 ≤ -n then a ((-n).toNat, i) else 0) := by
  rw [fourierCoeff_congr_ae (Lp.coeFn_star (hardyTraceLp a i))]
  change fourierCoeff (fun t => conj (hardyTraceLp a i t)) n = _
  rw [hardy_fourierCoeff_conj, hardyTrace_fourierCoeff]

theorem hardyTrace_product_mean (a b : HardySeq r) (i j : Fin r) :
    (∫ t, hardyTraceLp a i t * hardyTraceLp b j t ∂hardyCircleMeasure) =
      a (0, i) * b (0, j) := by
  let F := hardyTraceLp a i
  let G := hardyTraceLp b j
  have hi : inner ℂ (star F) G = ∫ t, F t * G t ∂hardyCircleMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star F] with t ht
    rw [RCLike.inner_apply', ht]
    simp only [Pi.star_apply, RCLike.star_def, Complex.conj_conj]
  have hre := (fourierBasis (T := 2 * Real.pi)).repr.inner_map_map (star F) G
  calc
    _ = inner ℂ (star F) G := hi.symm
    _ = inner ℂ ((fourierBasis (T := 2 * Real.pi)).repr (star F))
        ((fourierBasis (T := 2 * Real.pi)).repr G) := hre.symm
    _ = ∑' n : ℤ, inner ℂ ((fourierBasis (T := 2 * Real.pi)).repr (star F) n)
        ((fourierBasis (T := 2 * Real.pi)).repr G n) := lp.inner_eq_tsum _ _
    _ = inner ℂ ((fourierBasis (T := 2 * Real.pi)).repr (star F) 0)
        ((fourierBasis (T := 2 * Real.pi)).repr G 0) := by
      apply tsum_eq_single 0
      · intro n hn
        rw [fourierBasis_repr, fourierBasis_repr]
        change inner ℂ (fourierCoeff (star (hardyTraceLp a i) : Lp ℂ 2 hardyCircleMeasure) n)
          (fourierCoeff (hardyTraceLp b j) n) = 0
        rw [hardyTrace_star_fourier, hardyTrace_fourierCoeff]
        by_cases hp : 0 ≤ n
        · have hm : ¬ 0 ≤ -n := by omega
          simp only [hm, ite_false, map_zero, inner_zero_left]
        · simp only [hp, ite_false, inner_zero_right]
    _ = _ := by
      rw [fourierBasis_repr, fourierBasis_repr]
      change inner ℂ (fourierCoeff (star (hardyTraceLp a i) : Lp ℂ 2 hardyCircleMeasure) 0)
        (fourierCoeff (hardyTraceLp b j) 0) = _
      rw [hardyTrace_star_fourier, hardyTrace_fourierCoeff]
      simp only [neg_zero, le_refl, ite_true, Int.toNat_zero, RCLike.inner_apply', Complex.conj_conj]

end Yau.NodeProofs.D06Aux

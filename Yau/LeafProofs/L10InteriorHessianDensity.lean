import Yau.LeafProofs.L10InteriorHessianFinite

/-! The real and imaginary second-derivative energies are the original complex test. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Yau.LeafProofs

theorem elliptic_hessian_complex_absorption {ι : Type*} [Fintype ι]
    (a : ι → ι → ℝ) (E : ι → ι → ι → ℝ) (c d : ι → ℝ)
    (G : ι → ℂ) (H : ι → ι → ℂ) (f : ℂ) (e ell A B M : ℝ)
    (hell : 0 < ell) (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (ha : ∀ i j, |a i j| ≤ A) (hE : ∀ k i j, |E k i j| ≤ A)
    (hc : ∀ i, |c i| ≤ B) (hd : ∀ i, |d i| ≤ M) (he : |e| ≤ 1)
    (hEll : ∀ v : ι → ℝ, ell * ∑ i, (v i)^2 ≤ ∑ i, ∑ j, a i j * v i * v j) :
    ell / 2 * (e^2 * ∑ k, ∑ i, ‖H k i‖^2) ≤
      (ellipticHessianFiniteResidual a E c d (fun i => (G i).re) (fun k i => (H k i).re) e f.re +
        ellipticHessianFiniteResidual a E c d (fun i => (G i).im) (fun k i => (H k i).im) e f.im) +
      ellipticHessianAbsorptionConstant (Fintype.card ι) ell A B M *
        ((∑ i, ‖G i‖^2) + ‖f‖^2) := by
  have hr := elliptic_hessian_finite_absorption a E c d (fun i => (G i).re)
    (fun k i => (H k i).re) e f.re ell A B M hell hA hB hM ha hE hc hd he hEll
  have hi := elliptic_hessian_finite_absorption a E c d (fun i => (G i).im)
    (fun k i => (H k i).im) e f.im ell A B M hell hA hB hM ha hE hc hd he hEll
  have hnorm (z : ℂ) : ‖z‖^2 = z.re^2 + z.im^2 := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, pow_two]
  simp only [hnorm, Finset.sum_add_distrib]
  linarith

theorem ellipticHessianFiniteResidual_complex_test {ι : Type*} [Fintype ι]
    (a : ι → ι → ℝ) (E : ι → ι → ι → ℝ) (c d : ι → ℝ)
    (G : ι → ℂ) (H : ι → ι → ℂ) (f : ℂ) (e : ℝ) :
    ellipticHessianFiniteResidual a E c d (fun i => (G i).re) (fun k i => (H k i).re) e f.re +
      ellipticHessianFiniteResidual a E c d (fun i => (G i).im) (fun k i => (H k i).im) e f.im =
    ((∑ k, ∑ i, (e^2 • conj (H k i) + (2 * e * d i) • conj (G k)) *
      ((∑ j, (a i j : ℂ) * H k j) + ∑ j, (E k i j : ℂ) * G j)) -
      ∑ k, (e^2 • conj (H k k) + (2 * e * d k) • conj (G k)) *
        (f - ∑ j, (c j : ℂ) * G j)).re := by
  classical
  have hre (g : ι → ℝ) (v : ι → ℂ) : (∑ i, (g i : ℂ) * v i).re = ∑ i, g i * (v i).re := by
    change Complex.reCLM _ = _
    simp only [map_sum, Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  have him (g : ι → ℝ) (v : ι → ℂ) : (∑ i, (g i : ℂ) * v i).im = ∑ i, g i * (v i).im := by
    change Complex.imCLM _ = _
    simp only [map_sum, Complex.imCLM_apply, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
  have hpair (α β : ℝ) (z w v : ℂ) :
      ((α • conj z + β • conj w) * v).re =
        (α * z.re + β * w.re) * v.re + (α * z.im + β * w.im) * v.im := by
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.smul_re,
      Complex.smul_im, Complex.conj_re, Complex.conj_im]
    ring
  have hmainsum : (∑ k, ∑ i, (e^2 • conj (H k i) + (2 * e * d i) • conj (G k)) *
      ((∑ j, (a i j : ℂ) * H k j) + ∑ j, (E k i j : ℂ) * G j)).re =
      (∑ k, ∑ i, (e^2 * (H k i).re + 2 * e * d i * (G k).re) *
        ((∑ j, a i j * (H k j).re) + ∑ j, E k i j * (G j).re)) +
      ∑ k, ∑ i, (e^2 * (H k i).im + 2 * e * d i * (G k).im) *
        ((∑ j, a i j * (H k j).im) + ∑ j, E k i j * (G j).im) := by
    change Complex.reCLM _ = _
    simp only [map_sum, Complex.reCLM_apply, hpair, Complex.add_re,
      Complex.add_im, hre, him, Finset.sum_add_distrib]
  have hsourcesum : (∑ k, (e^2 • conj (H k k) + (2 * e * d k) • conj (G k)) *
      (f - ∑ j, (c j : ℂ) * G j)).re =
      (∑ k, (e^2 * (H k k).re + 2 * e * d k * (G k).re) * (f.re - ∑ j, c j * (G j).re)) +
      ∑ k, (e^2 * (H k k).im + 2 * e * d k * (G k).im) * (f.im - ∑ j, c j * (G j).im) := by
    change Complex.reCLM _ = _
    simp only [map_sum, Complex.reCLM_apply, hpair, Complex.sub_re,
      Complex.sub_im, hre, him, Finset.sum_add_distrib]
  rw [Complex.sub_re, hmainsum, hsourcesum]
  unfold ellipticHessianFiniteResidual
  ring

end Yau.LeafProofs

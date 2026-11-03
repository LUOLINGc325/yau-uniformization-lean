import Yau.LeafProofs.L10InteriorTest
import Yau.LeafProofs.L10InteriorEnergyAlgebra

/-! The finite real energy is exactly the real part of the actual complex test. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate BigOperators

namespace Yau.LeafProofs

theorem ellipticFiniteResidual_complex_test {ι : Type*} [Fintype ι]
    (a : ι → ι → ℝ) (c d : ι → ℝ) (H : ι → ℂ) (w f : ℂ) (e : ℝ) :
    ellipticFiniteResidual a c (fun i => (H i).re) d e w.re f.re +
      ellipticFiniteResidual a c (fun i => (H i).im) d e w.im f.im =
    ((∑ i, (e^2 • conj (H i) + (2 * e * d i) • conj w) *
      (∑ j, (a i j : ℂ) * H j)) + (e^2 • conj w) * (f - ∑ i, (c i : ℂ) * H i)).re := by
  classical
  have hre (g : ι → ℝ) : (∑ i, (g i : ℂ) * H i).re = ∑ i, g i * (H i).re := by
    change Complex.reCLM _ = _
    simp only [map_sum, Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  have him (g : ι → ℝ) : (∑ i, (g i : ℂ) * H i).im = ∑ i, g i * (H i).im := by
    change Complex.imCLM _ = _
    simp only [map_sum, Complex.imCLM_apply, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
  have hp (i : ι) :
      ((e^2 • conj (H i) + (2 * e * d i) • conj w) * (∑ j, (a i j : ℂ) * H j)).re =
        (e^2 * (H i).re + 2 * e * d i * w.re) * (∑ j, a i j * (H j).re) +
        (e^2 * (H i).im + 2 * e * d i * w.im) * (∑ j, a i j * (H j).im) := by
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.smul_re,
      Complex.smul_im, Complex.conj_re, Complex.conj_im, hre, him]
    ring
  have hmain : (∑ i, (e^2 • conj (H i) + (2 * e * d i) • conj w) *
      (∑ j, (a i j : ℂ) * H j)).re =
      (∑ i, (e^2 * (H i).re + 2 * e * d i * w.re) * (∑ j, a i j * (H j).re)) +
      ∑ i, (e^2 * (H i).im + 2 * e * d i * w.im) * (∑ j, a i j * (H j).im) := by
    change Complex.reCLM _ = _
    simp only [map_sum, Complex.reCLM_apply, hp, Finset.sum_add_distrib]
  have hsource : ((e^2 • conj w) * (f - ∑ i, (c i : ℂ) * H i)).re =
      e^2 * w.re * (f.re - ∑ i, c i * (H i).re) +
      e^2 * w.im * (f.im - ∑ i, c i * (H i).im) := by
    simp only [Complex.mul_re, Complex.smul_re, Complex.smul_im, Complex.conj_re,
      Complex.conj_im, Complex.sub_re, Complex.sub_im, hre, him]
    ring
  rw [ellipticFiniteResidual_eq_test, ellipticFiniteResidual_eq_test,
    Complex.add_re, hmain, hsource]
  ring

end Yau.LeafProofs

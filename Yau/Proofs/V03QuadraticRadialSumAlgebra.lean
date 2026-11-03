import Yau.Proofs.V03QuadraticRadialAlgebra

/-! The exact signed scalar radial expansion commutes with its genuine
finite ambient-coordinate contraction. -/

noncomputable section
namespace Yau.Blueprint.V03Proof

theorem quadratic_coefficient_radial_sum_algebra {ι : Type*} [Fintype ι]
    (u v : ℂ) (c₀ c₁ g : ι → ℂ) :
    (star u * (((2 * (∑ a, c₀ a * (-Complex.I * g a)).re : ℝ) : ℂ) +
      Complex.I * ((2 * (∑ a, c₁ a * (-Complex.I * g a)).re : ℝ) : ℂ)) * v).re =
      ∑ a, ((star u * (-Complex.I * c₀ a) * v * g a).re +
        (star v * (-Complex.I * c₀ a) * u * g a).re +
          (star u * c₁ a * v * g a).re - (star v * c₁ a * u * g a).re) := by
  have he : (((2 * (∑ a, c₀ a * (-Complex.I * g a)).re : ℝ) : ℂ) +
      Complex.I * ((2 * (∑ a, c₁ a * (-Complex.I * g a)).re : ℝ) : ℂ)) =
      ∑ a, ((((2 * (c₀ a * (-Complex.I * g a)).re : ℝ) : ℂ) +
        Complex.I * ((2 * (c₁ a * (-Complex.I * g a)).re : ℝ) : ℂ))) := by
    simp only [Complex.re_sum, Finset.mul_sum, Complex.ofReal_sum, Finset.sum_add_distrib]
  rw [he, Finset.mul_sum, Finset.sum_mul, Complex.re_sum]
  exact Finset.sum_congr rfl (fun a _ => quadratic_coefficient_radial_algebra u v (c₀ a) (c₁ a) (g a))

end Yau.Blueprint.V03Proof

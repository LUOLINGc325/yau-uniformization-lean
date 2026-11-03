import Yau.Proofs.V03QuadraticFieldDerivative

/-! Exact complex algebra expands the actual coefficient and velocity
radial jets into signed derivative currents of bounded scalar products. -/

noncomputable section
namespace Yau.Blueprint.V03Proof

theorem quadratic_coefficient_radial_algebra (u v c₀ c₁ g : ℂ) :
    (star u * (((2 * (c₀ * (-Complex.I * g)).re : ℝ) : ℂ) +
      Complex.I * ((2 * (c₁ * (-Complex.I * g)).re : ℝ) : ℂ)) * v).re =
      (star u * (-Complex.I * c₀) * v * g).re +
        (star v * (-Complex.I * c₀) * u * g).re +
          (star u * c₁ * v * g).re - (star v * c₁ * u * g).re := by
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem quadratic_velocity_radial_algebra (u v du dv B : ℂ) :
    (star (-Complex.I * du) * B * v + star u * B * (-Complex.I * dv)).re =
      (star v * (-Complex.I * star B) * du).re + (star u * (-Complex.I * B) * dv).re := by
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  ring

end Yau.Blueprint.V03Proof

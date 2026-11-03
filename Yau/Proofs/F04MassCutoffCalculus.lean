import Yau.Proofs.F04ManifoldLevi
import Yau.Proofs.F04MassProfileDeriv

open Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder

noncomputable section

namespace Yau.F04Proof

theorem massCutoff_levi_formula {n : ℕ} {M : ComplexManifold n} {u : M.Carrier → ℝ}
    (hu : SmoothFn u) (R : ℝ) (x : M.Carrier) :
    levi (massCutoff u R) x =
      (((deriv massProfile (u x / R) / R : ℝ) : ℂ)) • levi u x +
        (((deriv (deriv massProfile) (u x / R) / R ^ 2 : ℝ) : ℂ)) •
          Matrix.vecMulVec (star (manifoldComplexGradient u x)) (manifoldComplexGradient u x) := by
  have hF : ContDiff ℝ ∞ (fun s : ℝ => massProfile (s / R)) :=
    massProfile_smooth.comp (contDiff_id.div_const R)
  have hh := levi_real_comp hu (fun s => massProfile (s / R)) x (hF.contDiffAt.of_le (by norm_num))
  rw [massProfile_scaled_deriv, massProfile_scaled_secondDeriv] at hh
  exact hh

theorem massCutoff_complexGradient {n : ℕ} {M : ComplexManifold n} {u : M.Carrier → ℝ}
    (hu : SmoothFn u) (R : ℝ) (x : M.Carrier) :
    manifoldComplexGradient (massCutoff u R) x =
      scaleCovector (deriv massProfile (u x / R) / R) (manifoldComplexGradient u x) := by
  have hF : ContDiff ℝ ∞ (fun s : ℝ => massProfile (s / R)) :=
    massProfile_smooth.comp (contDiff_id.div_const R)
  have hd := (hF.differentiable (by simp) (u x)).hasDerivAt
  rw [massProfile_scaled_deriv] at hd
  exact manifold_gradient_real_comp hu (fun s => massProfile (s / R)) x hd

theorem massCutoff_gradNormSq {n : ℕ} {M : ComplexManifold n} (g : HermitianField M)
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (R : ℝ) (x : M.Carrier) :
    gradNormSq g (massCutoff u R) x =
      (deriv massProfile (u x / R) / R) ^ 2 * gradNormSq g u x := by
  have hF : ContDiff ℝ ∞ (fun s : ℝ => massProfile (s / R)) :=
    massProfile_smooth.comp (contDiff_id.div_const R)
  have hd := (hF.differentiable (by simp) (u x)).hasDerivAt
  rw [massProfile_scaled_deriv] at hd
  exact gradNormSq_real_comp g hu (fun s => massProfile (s / R)) x hd

theorem massCutoff_flat_off_shell {n : ℕ} {M : ComplexManifold n} {u : M.Carrier → ℝ}
    (hu : SmoothFn u) {R : ℝ} (hR : 0 < R) (x : M.Carrier) (hx : u x < R ∨ 2 * R < u x) :
    levi (massCutoff u R) x = 0 ∧ manifoldComplexGradient (massCutoff u R) x = 0 := by
  have hd := massProfile_scaled_flat hR hx
  rw [massProfile_scaled_deriv, massProfile_scaled_secondDeriv] at hd
  rw [massCutoff_levi_formula hu R x, massCutoff_complexGradient hu R x, hd.1, hd.2]
  simp only [Complex.ofReal_zero, zero_smul, zero_add, scaleCovector, and_self]

end Yau.F04Proof

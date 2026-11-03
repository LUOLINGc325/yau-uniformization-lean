import Yau.Proofs.P06LeviTests
import Yau.LeafProofs.L22LeviCalculus
import Yau.LeafProofs.L22Second

/-! Local real C² calculus for the directional Levi operator. -/

noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.P07DistanceLevi
open Yau Yau.Blueprint Yau.LeafProofs L18Aux L22Aux

variable {n : ℕ}

/-- The positive quadratic term in the real scalar Levi chain rule. -/
def directionalRankOne (f : ComplexVector n → ℝ) (z v : ComplexVector n) : ℝ :=
  ((fderiv ℝ f z v) ^ 2 + (fderiv ℝ f z (Complex.I • v)) ^ 2) / 4

theorem directionalRankOne_nonneg (f : ComplexVector n → ℝ) (z v : ComplexVector n) :
    0 ≤ directionalRankOne f z v := by
  unfold directionalRankOne
  positivity

/-- Scalar composition uses the paired real Hessian divided by four. -/
theorem leviDirection_scalar_comp {f : ComplexVector n → ℝ} {χ : ℝ → ℝ}
    {z : ComplexVector n} (hf : ContDiffAt ℝ 2 f z)
    (hχ : ContDiffAt ℝ 2 χ (f z)) (v : ComplexVector n) :
    leviDirection (leviC (χ ∘ f) z) v =
      deriv χ (f z) * leviDirection (leviC f z) v +
      deriv (deriv χ) (f z) * directionalRankOne f z v := by
  rw [leviDirection, leviC_quadratic_re (hχ.comp z hf),
    leviDirection, leviC_quadratic_re hf]
  simp only [complexLeviQuadratic, secondFDeriv_comp hf hχ,
    secondFDeriv_scalar_apply hχ, fderiv_eq_deriv_mul, directionalRankOne]
  ring

/-- A local minimum orders the actual Levi forms in each complex direction. -/
theorem leviDirection_le_of_localMin {S φ : ComplexVector n → ℝ}
    {z : ComplexVector n} (hS : ContDiffAt ℝ 2 S z)
    (hφ : ContDiffAt ℝ 2 φ z) (hmin : IsLocalMin (fun w => S w - φ w) z)
    (v : ComplexVector n) :
    leviDirection (leviC φ z) v ≤ leviDirection (leviC S z) v := by
  have hdiff := hS.sub hφ
  have h₁ := hessian_nonneg_of_localMin hdiff hmin v
  have h₂ := hessian_nonneg_of_localMin hdiff hmin (Complex.I • v)
  have heq (w : ComplexVector n) :
      fderiv ℝ (fderiv ℝ (fun y => S y - φ y)) z w w =
        fderiv ℝ (fderiv ℝ S) z w w - fderiv ℝ (fderiv ℝ φ) z w w := by
    have hh : (fun y => S y - φ y) = (fun y => S y + (-1) * φ y) := by
      funext y
      ring
    rw [hh, secondFDeriv_add hS (contDiffAt_const.mul hφ),
      secondFDeriv_const_mul hφ]
    ring
  rw [heq] at h₁ h₂
  rw [leviDirection, leviC_quadratic_re hφ, leviDirection, leviC_quadratic_re hS]
  unfold complexLeviQuadratic
  linarith

/-- An upper support controls lower tests. The reversed test orientation is
deliberately absent: it is false for a nonsmooth function. -/
theorem leviDirection_lowerTest_of_upperSupport
    {f S φ : ComplexVector n → ℝ} {z : ComplexVector n}
    (hS : ContDiffAt ℝ 2 S z) (hφ : ContDiffAt ℝ 2 φ z)
    (hSf : ∀ᶠ w in 𝓝 z, f w ≤ S w) (hφf : ∀ᶠ w in 𝓝 z, φ w ≤ f w)
    (hSz : S z = f z) (hφz : φ z = f z) (v : ComplexVector n) :
    leviDirection (leviC φ z) v ≤ leviDirection (leviC S z) v := by
  apply leviDirection_le_of_localMin hS hφ
  change ∀ᶠ w in 𝓝 z, S z - φ z ≤ S w - φ w
  filter_upwards [hSf, hφf] with w hw hw'
  rw [hSz, hφz, sub_self]
  exact sub_nonneg.mpr (hw'.trans hw)

end Yau.NodeProofs.P07DistanceLevi

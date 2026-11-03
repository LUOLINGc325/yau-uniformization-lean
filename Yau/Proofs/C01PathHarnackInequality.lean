import Yau.Proofs.C01PathFactorAlgebra

/-! The original differential Harnack inequality along a path after
the actual time change, with speed measured in the initial metric. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

theorem quadratic_real_smul {n : ℕ} (H : Herm n) (v : ComplexVector n) (r : ℝ) :
    (star (WithLp.ofLp (r • v)) ⬝ᵥ (H *ᵥ WithLp.ofLp (r • v))).re =
      r ^ 2 * (star (WithLp.ofLp v) ⬝ᵥ (H *ᵥ WithLp.ofLp v)).re := by
  have hv : WithLp.ofLp (r • v) = (r : ℂ) • WithLp.ofLp v := by
    ext i
    change r • v i = (r : ℂ) * v i
    simp only [Complex.real_smul, smul_eq_mul]
  have heq : star (WithLp.ofLp (r • v)) ⬝ᵥ (H *ᵥ WithLp.ofLp (r • v)) =
      ((r ^ 2 : ℝ) : ℂ) * (star (WithLp.ofLp v) ⬝ᵥ (H *ᵥ WithLp.ofLp v)) := by
    rw [hv, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_smul]
    simp [smul_eq_mul, pow_two, mul_assoc]
  rw [heq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_scalar_nonneg
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ scalarCurvature (h t) x := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hR, _⟩ := hflow
  exact (hR x t ht).2

theorem localizedFlow_scalar_rescaled_harnack
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (x : Pt X) (t : ℝ) (ht : 0 < t) (d : ComplexVector n) (a : ℝ) :
    0 ≤ deriv (fun u => scalarCurvature (h u) x) t + t⁻¹ * scalarCurvature (h t) x +
      a⁻¹ * (2 * (∑ i, d i * wirt
        (fun z => Complex.ofReal (inChart x (scalarCurvature (h t)) z)) (chartPt x x) (stdVec i)).re) +
      (a⁻¹) ^ 2 * scalarCurvature (h t) x *
        (star (WithLp.ofLp d) ⬝ᵥ (gMat (h t) x *ᵥ WithLp.ofLp d)).re := by
  have hh := localizedFlow_scalar_metric_harnack hflow hjoint x ht (a⁻¹ • d)
  rw [← wirt_stdVec_sum, Yau.Blueprint.Alignment.Y03Proof.wirt_real_smul_dir,
    quadratic_real_smul] at hh
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hh
  rw [wirt_stdVec_sum] at hh
  nlinarith only [hh]

theorem localizedFlow_path_speed_harnack
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    {x₀ x₁ : Pt X} (γ : PiecewiseC1Curve x₀ x₁) (s t₀ t a : ℝ)
    (ht₀ : 0 ≤ t₀) (ht : 0 < t) (ht₀t : t₀ ≤ t) :
    0 ≤ deriv (fun u => scalarCurvature (h u) (γ s)) t + t⁻¹ * scalarCurvature (h t) (γ s) +
      a⁻¹ * (2 * (∑ i, pathChartVelocity γ s i * wirt
        (fun z => Complex.ofReal (inChart (γ s) (scalarCurvature (h t)) z))
          (chartPt (γ s) (γ s)) (stdVec i)).re) +
      (a⁻¹) ^ 2 * scalarCurvature (h t) (γ s) * (curveSpeed (h t₀) γ s ^ 2 / 2) := by
  have hh := localizedFlow_scalar_rescaled_harnack hflow hjoint (γ s) t ht (pathChartVelocity γ s) a
  have hq := localizedFlow_path_metric_quadratic_le hflow hjoint γ s t₀ t ht₀ ht₀t
  have hm := mul_le_mul_of_nonneg_left hq
    (mul_nonneg (sq_nonneg a⁻¹) (localizedFlow_scalar_nonneg hflow (γ s) t ht.le))
  linarith

end Yau.NodeProofs.C01Aux

import Yau.Proofs.P07DistanceLeviRankOne

noncomputable section
open Filter
open scoped Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.P07DistanceLevi
open Yau Yau.Blueprint Yau.LeafProofs L18Aux L22Aux

variable {n : ℕ}

theorem leviDirection_const_mul {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (c : ℝ) (v : ComplexVector n) :
    leviDirection (leviC (fun w => c * f w) z) v = c * leviDirection (leviC f z) v := by
  rw [leviDirection, leviC_quadratic_re (contDiffAt_const.mul hf),
    complexLeviQuadratic_const_mul hf, leviDirection, leviC_quadratic_re hf]

theorem directionalRankOne_const_mul {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : DifferentiableAt ℝ f z) (c : ℝ) (v : ComplexVector n) :
    directionalRankOne (fun w => c * f w) z v = c ^ 2 * directionalRankOne f z v := by
  simp only [directionalRankOne, fderiv_const_mul hf, smul_apply, smul_eq_mul]
  ring

theorem secondDeriv_eq_zero_of_right_plateau {χ : ℝ → ℝ} {b s : ℝ}
    (hplateau : ∀ t, b ≤ t → χ t = 1) (hs : b < s) : deriv (deriv χ) s = 0 := by
  have heq : χ =ᶠ[𝓝 s] (fun _ => (1 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact hplateau t ht.le
  simpa only [deriv_const'] using heq.deriv.deriv_eq

theorem metricLeviDirection_nonneg {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (v : ComplexVector n) :
    0 ≤ leviDirection (hMat h x z) v :=
  (Complex.nonneg_iff.mp ((L18Aux.hMat_posDef h x z hz).posSemidef.dotProduct_mulVec_nonneg
    (WithLp.ofLp v))).1

/-- The scalar estimate retains the safe physical-gradient factor two.
The right plateau eliminates the unbounded-radius second derivative term. -/
theorem scalar_scaled_chain_upper
    {a b c ℓ R H r₂ L A₁ A₂ : ℝ}
    (ha : 0 ≤ a) (haA : a ≤ A₁) (hbA : b ≤ A₂) (hA₂ : 0 ≤ A₂)
    (hc : 0 < c) (hcancel : c * L ^ 2 = 1) (hH : 0 ≤ H)
    (hℓ : ℓ ≤ 2 * H) (hR0 : 0 ≤ R) (hR : R ≤ 4 * r₂ * H)
    (hradius : r₂ ≤ 4 * L ^ 2 ∨ b = 0) :
    a * (c * ℓ) + b * (c ^ 2 * R) ≤ (2 * A₁ + 16 * A₂) * c * H := by
  have hfirst : a * (c * ℓ) ≤ 2 * A₁ * c * H := by
    calc
      a * (c * ℓ) = (a*c)*ℓ := by ring
      _ ≤ (a*c)*(2*H) := mul_le_mul_of_nonneg_left hℓ (mul_nonneg ha hc.le)
      _ = (2*c*H)*a := by ring
      _ ≤ (2*c*H)*A₁ := mul_le_mul_of_nonneg_left haA (by positivity)
      _ = _ := by ring
  have hsecond : b * (c^2 * R) ≤ 16*A₂*c*H := by
    rcases hradius with hradius | rfl
    · have hcancel₂ : c^2 * L^2 = c := by
        calc
          _ = c * (c * L^2) := by ring
          _ = c := by rw [hcancel,mul_one]
      have hcRadius := mul_le_mul_of_nonneg_left hradius (sq_nonneg c)
      have hnum : c^2*r₂ ≤ 4*c := by nlinarith only [hcRadius,hcancel₂]
      have hRR : c^2*R ≤ 16*c*H := by
        calc
          _ ≤ c^2*(4*r₂*H) := mul_le_mul_of_nonneg_left hR (sq_nonneg c)
          _ = 4*(c^2*r₂)*H := by ring
          _ ≤ 4*(4*c)*H := by gcongr
          _ = _ := by ring
      calc
        b*(c^2*R) ≤ A₂*(c^2*R) := mul_le_mul_of_nonneg_right hbA (by positivity)
        _ ≤ A₂*(16*c*H) := mul_le_mul_of_nonneg_left hRR hA₂
        _ = _ := by ring
    · simp only [zero_mul]
      positivity
  nlinarith only [hfirst,hsecond]

end Yau.NodeProofs.P07DistanceLevi

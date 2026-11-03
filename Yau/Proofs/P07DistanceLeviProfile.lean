import Yau.Proofs.P07DistanceLeviSupport
import Yau.Proofs.P07DistanceLeviScaling

noncomputable section
open Filter
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.P07DistanceLevi
open Yau Yau.Blueprint Yau.LeafProofs L12Aux

variable {n : ℕ}

/-- Applying a fixed monotone scalar truncation to the actual distance
energy supports gives a uniform local Levi bound before choosing a scale. -/
theorem radialTruncation_localUpperSupports (X : KahlerManifold n) (o : Pt X)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hmono : Monotone χ)
    (hone : ∀ s : ℝ, 4 ≤ s → χ s = 1)
    (A₁ A₂ : ℝ) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hbound : ∀ s : ℝ, |deriv χ s| ≤ A₁ ∧ |deriv (deriv χ) s| ≤ A₂) :
    ∃ A : ℝ, 0 < A ∧ ∀ L : ℝ, 0 < L → ∀ c : Pt X,
      ∀ z : ComplexVector n, z ∈ chartTarget c →
      ∃ S : ComplexVector n → ℝ,
        ContDiffAt ℝ 2 S z ∧
        S z = χ ((distFrom X.metric.form o (chartInv c z)) ^ 2 / L ^ 2) ∧
        (∀ᶠ w in 𝓝 z, χ ((distFrom X.metric.form o (chartInv c w)) ^ 2 / L ^ 2) ≤ S w) ∧
        ∀ v : ComplexVector n, leviDirection (leviC S z) v ≤
          (A / L ^ 2) * leviDirection (hMat X.metric.form c z) v := by
  let A := 1 + 2*A₁ + 16*A₂
  refine ⟨A,by dsimp [A]; positivity,?_⟩
  intro L hL c z hz
  obtain ⟨E,hE,hvalue,hupper,hLevi,hRank⟩ := distanceSquare_upperSupport_inChart X o c hz
  let d := (L ^ 2)⁻¹
  have hL₂ : 0 < L ^ 2 := pow_pos hL 2
  have hd : 0 < d := inv_pos.mpr hL₂
  have hcancel : d * L ^ 2 = 1 := inv_mul_cancel₀ hL₂.ne'
  let S := χ ∘ (fun w : ComplexVector n => d * E w)
  have hScaled : ContDiffAt ℝ 2 (fun w => d * E w) z := contDiffAt_const.mul hE
  have hOuter : ContDiffAt ℝ 2 χ (d * E z) := hχ.contDiffAt.of_le (by simp)
  refine ⟨S,hOuter.comp z hScaled,?_,?_,?_⟩
  · change χ (d * E z) = _
    rw [hvalue]
    congr 1
    dsimp only [d]
    ring
  · filter_upwards [hupper] with w hw
    apply hmono
    change (distFrom X.metric.form o (chartInv c w)) ^ 2 / L ^ 2 ≤ d * E w
    calc
      _ = d * (distFrom X.metric.form o (chartInv c w)) ^ 2 := by dsimp [d]; ring
      _ ≤ d * E w := mul_le_mul_of_nonneg_left hw hd.le
  · intro v
    change leviDirection (leviC (χ ∘ (fun w => d * E w)) z) v ≤ _
    rw [leviDirection_scalar_comp hScaled hOuter,
      leviDirection_const_mul hE,
      directionalRankOne_const_mul (hE.differentiableAt (by norm_num))]
    have hα : 0 ≤ deriv χ (d * E z) := hmono.deriv_nonneg
    have hαA : deriv χ (d * E z) ≤ A₁ := (le_abs_self _).trans (hbound _).1
    have hβA : deriv (deriv χ) (d * E z) ≤ A₂ := (le_abs_self _).trans (hbound _).2
    have hH := metricLeviDirection_nonneg X.metric.form c hz v
    have hradius : (distFrom X.metric.form o (chartInv c z)) ^ 2 ≤ 4 * L ^ 2 ∨
        deriv (deriv χ) (d * E z) = 0 := by
      by_cases hr : (distFrom X.metric.form o (chartInv c z)) ^ 2 ≤ 4 * L ^ 2
      · exact Or.inl hr
      · right
        apply secondDeriv_eq_zero_of_right_plateau hone
        rw [hvalue]
        have H := mul_lt_mul_of_pos_left (lt_of_not_ge hr) hd
        nlinarith only [H,hcancel]
    have H := scalar_scaled_chain_upper hα hαA hβA hA₂ hd hcancel hH (hLevi v)
      (directionalRankOne_nonneg E z v) (hRank v) hradius
    have hmore : (2*A₁+16*A₂)*d*leviDirection (hMat X.metric.form c z) v ≤
        A*d*leviDirection (hMat X.metric.form c z) v := by
      have hp := mul_nonneg hd.le hH
      dsimp only [A]
      nlinarith only [hp]
    have hAD : (A / L ^ 2) * leviDirection (hMat X.metric.form c z) v =
        A*d*leviDirection (hMat X.metric.form c z) v := by dsimp only [d]; ring
    rw [hAD]
    exact H.trans hmore

end Yau.NodeProofs.P07DistanceLevi

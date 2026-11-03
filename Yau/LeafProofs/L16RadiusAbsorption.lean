import Yau.LeafProofs.L16LowJetInterpolation

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- Radius-dependent interpolation parameters yield a uniform integer-power
    absorption step; no solution or Holder seminorm enters their choice. -/
theorem exists_radius_absorption_parameters {α A : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A) :
    ∃ P : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ρ ≤ h/4 ∧
      ∀ K B F : ℝ, 0 ≤ K → 0 ≤ B → 0 ≤ F →
        A*(h⁻¹)^8*(F+8*(ρ^(1-α)*K+ρ^(-1-α)*B)) ≤
          (2^(P+1) : ℝ)⁻¹*K+C*(h⁻¹)^P*(B+F) := by
  let q : ℝ := 1-α
  have hq : 0 < q := by dsimp only [q]; linarith
  obtain ⟨P,hP⟩ := exists_nat_ge (max (8 : ℝ) (16/q))
  have hP8 : (8 : ℝ) ≤ P := (le_max_left _ _).trans hP
  have hPp : 16/q ≤ P := (le_max_right _ _).trans hP
  have hP8Nat : 8 ≤ P := by exact_mod_cast hP8
  let θ : ℝ := (2^(P+1) : ℝ)⁻¹
  have hθ : 0 < θ := by dsimp only [θ]; positivity
  let ratio : ℝ := θ/(8*A)
  have hRatio : 0 < ratio := by dsimp only [ratio]; positivity
  let c : ℝ := min (1/8) (ratio^(q⁻¹))
  have hc : 0 < c := by dsimp only [c]; positivity
  have hcCap : c ≤ 1/8 := min_le_left _ _
  have hcRoot : c ≤ ratio^(q⁻¹) := min_le_right _ _
  have hRootPow : (ratio^(q⁻¹))^q = ratio := by
    rw [← Real.rpow_mul hRatio.le,inv_mul_cancel₀ hq.ne',Real.rpow_one]
  have hcPow : c^q ≤ ratio :=
    (Real.rpow_le_rpow hc.le hcRoot hq.le).trans_eq hRootPow
  have hcSmall : 8*A*c^q ≤ θ := by
    have h := (le_div_iff₀ (by positivity : 0 < 8*A)).mp hcPow
    nlinarith
  let C : ℝ := A+8*A*c^(-1-α)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨P,C,hC,?_⟩
  intro h hh hh1
  let ρ : ℝ := c*h^(8/q)
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hExp : 1 ≤ 8/q := (le_div_iff₀ hq).mpr (by dsimp only [q]; linarith)
  have hPowH : h^(8/q) ≤ h := Real.rpow_le_self_of_le_one hh.le hh1 hExp
  have hρCap : ρ ≤ h/8 := by
    calc
      ρ ≤ c*h := mul_le_mul_of_nonneg_left hPowH hc.le
      _ ≤ (1/8)*h := mul_le_mul_of_nonneg_right hcCap hh.le
      _ = h/8 := by ring
  have hρ1 : ρ ≤ 1 := hρCap.trans (by linarith)
  have hρMargin : ρ ≤ h/4 := hρCap.trans (by linarith)
  refine ⟨ρ,hρ,hρ1,hρMargin,?_⟩
  intro K B F hK hB hF
  have hRhoQ : ρ^q = c^q*h^(8 : ℝ) := by
    dsimp only [ρ]
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg hh.le _),← Real.rpow_mul hh.le]
    congr 1
    field_simp
  have hCancel : (h⁻¹)^8*h^(8 : ℝ) = 1 := by
    rw [Real.rpow_ofNat]
    field_simp
  have hKCoeff : 8*A*(h⁻¹)^8*ρ^q ≤ θ := by
    rw [hRhoQ]
    calc
      _ = (8*A*c^q)*((h⁻¹)^8*h^(8 : ℝ)) := by ring
      _ = 8*A*c^q := by rw [hCancel,mul_one]
      _ ≤ θ := hcSmall
  have hInvPow (j : ℕ) : (h⁻¹)^j = h^(-(j : ℝ)) := by
    rw [Real.rpow_neg hh.le,Real.rpow_natCast,inv_pow]
  have hRhoNeg : ρ^(-1-α) = c^(-1-α)*h^((8/q)*(-1-α)) := by
    dsimp only [ρ]
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg hh.le _),← Real.rpow_mul hh.le]
  have hExponent : -(8 : ℝ)+(8/q)*(-1-α) = -(16/q) := by
    dsimp only [q]
    field_simp
    ring
  have hBPower : (h⁻¹)^8*ρ^(-1-α) = c^(-1-α)*h^(-(16/q)) := by
    rw [hRhoNeg,hInvPow 8]
    calc
      _ = c^(-1-α)*(h^(-(8 : ℝ))*h^((8/q)*(-1-α))) := by ring
      _ = c^(-1-α)*h^(-(8 : ℝ)+(8/q)*(-1-α)) := by rw [← Real.rpow_add hh]
      _ = _ := by rw [hExponent]
  have hPowerP : h^(-(16/q)) ≤ (h⁻¹)^P := by
    rw [hInvPow P]
    exact Real.rpow_le_rpow_of_exponent_ge hh hh1 (by linarith)
  have hBCoeff : 8*A*(h⁻¹)^8*ρ^(-1-α) ≤ (8*A*c^(-1-α))*(h⁻¹)^P := by
    calc
      _ = 8*A*((h⁻¹)^8*ρ^(-1-α)) := by ring
      _ = (8*A*c^(-1-α))*h^(-(16/q)) := by rw [hBPower]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hPowerP (by positivity)
  have hInv : 1 ≤ h⁻¹ := (one_le_inv₀ hh).mpr hh1
  have hFCoeff : A*(h⁻¹)^8 ≤ A*(h⁻¹)^P :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hInv hP8Nat) hA.le
  have hFBound := mul_le_mul_of_nonneg_right hFCoeff hF
  have hKBound := mul_le_mul_of_nonneg_right hKCoeff hK
  have hBBound := mul_le_mul_of_nonneg_right hBCoeff hB
  change A*(h⁻¹)^8*(F+8*(ρ^q*K+ρ^(-1-α)*B)) ≤ _
  calc
    _ = A*(h⁻¹)^8*F+(8*A*(h⁻¹)^8*ρ^q)*K+(8*A*(h⁻¹)^8*ρ^(-1-α))*B := by ring
    _ ≤ A*(h⁻¹)^P*F+θ*K+(8*A*c^(-1-α))*(h⁻¹)^P*B :=
      add_le_add (add_le_add hFBound hKBound) hBBound
    _ ≤ θ*K+C*(h⁻¹)^P*(B+F) := by
      dsimp only [C]
      have hCross1 : 0 ≤ A*(h⁻¹)^P*B := by positivity
      have hCross2 : 0 ≤ (8*A*c^(-1-α))*(h⁻¹)^P*F := by positivity
      nlinarith

end Yau.LeafProofs.L16Aux

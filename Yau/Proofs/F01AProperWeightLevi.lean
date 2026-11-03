import Yau.Proofs.F01LaplacianLinearity

/-! A small square penalty retains half of the original metric in the
comparison heat operator. All constants precede the space-time point. -/
noncomputable section
open scoped ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem penalized_original_majorant_levi
    (g : HermitianField M) (Ξ u : M.Carrier → ℝ)
    (hΞ : SmoothFn Ξ) (hu : SmoothFn u) {B D ε A : ℝ}
    (hD : 0 ≤ D) (hε : 0 ≤ ε) (hbudget : D * ε * B ≤ 1 / 2)
    (hRic : ∀ x, HermLE (ricci g x) (levi Ξ x))
    (hsquare : ∀ x, HermLE (levi (fun y => u y ^ 2) x) ((B : ℂ) • gMat g x))
    (x : M.Carrier) :
    (gMat g x - (D : ℂ) • ricci g x +
      (D : ℂ) • levi (fun y => Ξ y - ε * u y ^ 2 - A) x -
      ((1 / 2 : ℝ) : ℂ) • gMat g x).PosSemidef := by
  have hu2 : SmoothFn (fun y => u y ^ 2) := fun a => (hu a).pow 2
  have hεu2 : SmoothFn (fun y => ε * u y ^ 2) :=
    fun a => contDiffOn_const.mul (hu2 a)
  have hdiff : SmoothFn (fun y => Ξ y - ε * u y ^ 2) := fun a => (hΞ a).sub (hεu2 a)
  have hA : SmoothFn (fun _ : M.Carrier => A) := fun _ => contDiffOn_const
  have hlevi : levi (fun y => Ξ y - ε * u y ^ 2 - A) x =
      levi Ξ x - (ε : ℂ) • levi (fun y => u y ^ 2) x := by
    rw [levi_sub_native hdiff hA, levi_const_native, sub_zero,
      levi_sub_native hΞ hεu2, levi_const_mul_native hu2 ε]
  have hremaining : 0 ≤ 1 - 1 / 2 - D * ε * B := by linarith
  have hG : (gMat g x).PosDef :=
    LeafProofs.L12Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x)
  have p1 := hG.posSemidef.smul (Complex.zero_le_real.mpr hremaining)
  have p2 := (show (levi Ξ x - ricci g x).PosSemidef from hRic x).smul
    (Complex.zero_le_real.mpr hD)
  have p3 := (show ((B : ℂ) • gMat g x - levi (fun y => u y ^ 2) x).PosSemidef
      from hsquare x).smul (Complex.zero_le_real.mpr (mul_nonneg hD hε))
  rw [hlevi]
  convert p2.add (p3.add p1) using 1
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- Shrinking the admissible comparison constant leaves room for both epsilon
and epsilon/2, and also supplies the half-metric heat lower bound. -/
theorem exists_proper_weight_parameter {D B η : ℝ}
    (hD : 0 < D) (hB : 0 < B) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ η / (D + 1) ∧
      ε / 2 ≤ η / (D + 1) ∧ D * ε * B ≤ 1 / 2 := by
  let ζ := min η (min 1 (1 / (2 * (B + 1))))
  have hζ : 0 < ζ := lt_min hη (lt_min zero_lt_one (by positivity))
  have hζη : ζ ≤ η := min_le_left _ _
  have hζB : ζ ≤ 1 / (2 * (B + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  let ε := ζ / (2 * (D + 1))
  have hε : 0 < ε := div_pos hζ (by positivity)
  have hεsmall : ε ≤ η / (D + 1) := by
    calc
      ε = (ζ / (D + 1)) / 2 := by
        dsimp only [ε]
        rw [div_div]
        congr 1
        ring
      _ ≤ ζ / (D + 1) := half_le_self (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_right hζη (by positivity)
  refine ⟨ε, hε, hεsmall, (half_le_self hε.le).trans hεsmall, ?_⟩
  have hζmul := (le_div_iff₀ (by positivity : 0 < 2 * (B + 1))).mp hζB
  have hζB1 : ζ * B ≤ 1 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hζB1 hD.le
  have heq : D * ε * B = ζ * (D * B) / (2 * (D + 1)) := by dsimp only [ε]; ring
  rw [heq]
  apply (div_le_iff₀ (by positivity : 0 < 2 * (D + 1))).mpr
  nlinarith

end Yau.NodeProofs.F01Aux

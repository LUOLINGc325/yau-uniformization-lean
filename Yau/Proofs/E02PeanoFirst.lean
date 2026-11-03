import Yau.Proofs.E02PeanoJet

open Set Filter Asymptotics
open scoped Topology Asymptotics
noncomputable section
namespace Yau.NodeProofs.E02Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem continuous_bilinear_diagonal_bigO (A : E →L[ℝ] E →L[ℝ] ℝ) (x : E) :
    (fun y => A (y-x) (y-x)) =O[𝓝 x] (fun y => ‖y-x‖^2) := by
  apply IsBigO.of_bound ‖A‖
  apply Eventually.of_forall
  intro y
  calc
    ‖A (y-x) (y-x)‖ ≤ ‖A‖*‖y-x‖*‖y-x‖ := A.le_opNorm₂ (y-x) (y-x)
    _ = ‖A‖*‖‖y-x‖^2‖ := by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖y-x‖)]
      ring

/-- A Peano expansion supplies a genuine first derivative. It supplies
no assertion that the jet tensor is a second Frechet derivative. -/
theorem realSecondJet_hasFDerivAt {f : E → ℝ} {x : E} {p : E →L[ℝ] ℝ}
    {A : E →L[ℝ] E →L[ℝ] ℝ} (hf : RealSecondJet f x p A) : HasFDerivAt f p x := by
  have hSq : (fun y : E => ‖y-x‖^2) =o[𝓝 x] (fun y => y-x) :=
    isLittleO_pow_sub_sub x (by norm_num : 1 < (2 : ℕ))
  have hRem := hf.2.trans hSq
  have hQuad := (continuous_bilinear_diagonal_bigO A x).trans_isLittleO hSq
  apply HasFDerivAt.of_isLittleO
  convert hRem.add (hQuad.const_mul_left (1/2)) using 1
  funext y
  ring

theorem realSecondJet_localMin_linear_zero {f : E → ℝ} {x : E} {p : E →L[ℝ] ℝ}
    {A : E →L[ℝ] E →L[ℝ] ℝ} (hf : RealSecondJet f x p A) (hmin : IsLocalMin f x) :
    p = 0 := hmin.hasFDerivAt_eq_zero (realSecondJet_hasFDerivAt hf)

/-- Genuine lower and upper polynomial contacts, for every positive
quadratic error, obtained directly from the actual Peano remainder. -/
theorem realSecondJet_quadratic_bounds {f : E → ℝ} {x : E} {p : E →L[ℝ] ℝ}
    {A : E →L[ℝ] E →L[ℝ] ℝ} (hf : RealSecondJet f x p A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 x,
      f x+p (y-x)+(1/2)*A (y-x) (y-x)-ε*‖y-x‖^2 ≤ f y ∧
      f y ≤ f x+p (y-x)+(1/2)*A (y-x) (y-x)+ε*‖y-x‖^2 := by
  filter_upwards [hf.2.def hε] with y hy
  have hb : |f y-f x-p (y-x)-(1/2)*A (y-x) (y-x)| ≤ ε*‖y-x‖^2 := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖y-x‖)] using hy
  constructor
  · linarith [(abs_le.mp hb).1]
  · linarith [(abs_le.mp hb).2]

end Yau.NodeProofs.E02Aux

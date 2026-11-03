import Yau.LeafProofs.L19LocalizationEvolution

/-! Actual scalar differential algebra for the explicit lateral boundary barrier. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L18Aux LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

def boundaryBarrier (r q : M.Carrier → ℝ) (κ : ℝ) (x : M.Carrier) : ℝ :=
  r x + (-κ) * (r x * r x) + q x

theorem boundaryBarrier_smooth {r q : M.Carrier → ℝ}
    (hr : SmoothFn r) (hq : SmoothFn q) (κ : ℝ) : SmoothFn (boundaryBarrier r q κ) := by
  intro a
  exact ((hr a).add (contDiffOn_const.mul ((hr a).mul (hr a)))).add (hq a)

theorem boundaryBarrier_laplacian (g : HermitianField M) {r q : M.Carrier → ℝ}
    (hr : SmoothFn r) (hq : SmoothFn q) (κ : ℝ) (x : M.Carrier) :
    laplacian g (boundaryBarrier r q κ) x =
      (1 - 2 * κ * r x) * laplacian g r x -
        κ * scalarGradientPair g r r x + laplacian g q x := by
  have hmid : SmoothFn (fun y => r y + (-κ) * (r y * r y)) :=
    fun a => (hr a).add (contDiffOn_const.mul ((hr a).mul (hr a)))
  unfold boundaryBarrier
  rw [laplacian_add g hmid hq, laplacian_add g hr
    (fun a => contDiffOn_const.mul ((hr a).mul (hr a))),
    laplacian_const_mul g (smoothFn_mul hr hr), laplacian_mul g hr hr]
  unfold scalarGradientPair
  ring

theorem boundaryBarrier_lower {r q : M.Carrier → ℝ} (κ : ℝ) (x : M.Carrier)
    (hr : 0 ≤ r x) (hκr : κ * r x ≤ 1 / 2) :
    r x / 2 + q x ≤ boundaryBarrier r q κ x := by
  have hmul := mul_le_mul_of_nonneg_right hκr hr
  unfold boundaryBarrier
  nlinarith only [hmul]

theorem boundaryBarrier_at_boundary {r q : M.Carrier → ℝ} (κ : ℝ) (x : M.Carrier)
    (hr : r x = 0) (hq : q x = 0) : boundaryBarrier r q κ x = 0 := by
  simp only [boundaryBarrier, hr, hq, mul_zero, zero_add]

/-- Once the genuine defining function has a positive gradient bound, the
explicit quadratic correction has a strict actual Laplacian sign. -/
theorem boundaryBarrier_neg_laplacian (g : HermitianField M) {r q : M.Carrier → ℝ}
    (hr : SmoothFn r) (hq : SmoothFn q) (κ A b : ℝ) (x : M.Carrier)
    (hκ : 0 ≤ κ) (hA : 0 ≤ A) (hrx : 0 ≤ r x) (hκr : 2 * κ * r x ≤ 1)
    (hlapr : laplacian g r x ≤ A) (hlapq : laplacian g q x ≤ A)
    (hgrad : b ≤ scalarGradientPair g r r x) (hlarge : 2 * A + 1 ≤ κ * b) :
    1 ≤ -laplacian g (boundaryBarrier r q κ) x := by
  have hc₀ : 0 ≤ 1 - 2 * κ * r x := by linarith
  have hc₁ : 1 - 2 * κ * r x ≤ 1 := by nlinarith only [hκ, hrx]
  have hc := (mul_le_mul_of_nonneg_left hlapr hc₀).trans
    (mul_le_of_le_one_left hA hc₁)
  have hg := mul_le_mul_of_nonneg_left hgrad hκ
  rw [boundaryBarrier_laplacian g hr hq]
  linarith only [hc, hg, hlapq, hlarge]

end Yau.Proofs.F03Aux

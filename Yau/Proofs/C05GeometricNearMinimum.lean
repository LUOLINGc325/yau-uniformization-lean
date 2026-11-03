import Yau.Proofs.C05GeometricNearMinimumFinite

/-! The radius is fixed before taking the limit of the center values. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05GeometricNearMinimumAux
open Yau Yau.Proofs.C05Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem eventually_laplacian_lower (o : M.Carrier) (g : ℕ → SmoothMetric M)
    (f : ℕ → M.Carrier → ℝ) (hf : ∀ i, SmoothFn (f i)) {r J : ℝ}
    (hr : 0 < r) (hJ : 0 ≤ J)
    (hB3 : ∀ i x, x ∈ distBall (g i).form o r →
      scalarJetNorm (g i).form (f i) 3 x ≤ J)
    (hnonneg : ∀ i x, x ∈ distBall (g i).form o r → 0 ≤ f i x)
    (hzero : Tendsto (fun i => f i o) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ i in atTop, -ε ≤ laplacian (g i).form (f i) o := by
  intro ε hε
  let a : ℝ := (n : ℝ)*J/3
  have ha : 0 ≤ a := by dsimp [a]; positivity
  let h : ℝ := min (r/2) (ε/(2*(a+1)))
  have hh : 0 < h := lt_min (by positivity) (by positivity)
  have hhr : h < r := (min_le_left _ _).trans_lt (by linarith)
  have hah : a*h ≤ ε/2 := by
    have H := (le_div_iff₀ (show 0 < 2*(a+1) by positivity)).mp
      (min_le_right (r/2) (ε/(2*(a+1))))
    change h * (2*(a+1)) ≤ ε at H
    nlinarith
  let b : ℝ := 2*(n : ℝ)/h^2
  have ht : Tendsto (fun i => b*f i o) atTop (𝓝 0) := by
    simpa only [mul_zero] using hzero.const_mul b
  have hsmall : ∀ᶠ i in atTop, b*f i o < ε/2 :=
    ht.eventually (gt_mem_nhds (show (0:ℝ) < ε/2 by positivity))
  filter_upwards [hsmall] with i hi
  have H := laplacian_finite_step_lower (g i) (f i) (hf i) o hr
    (hB3 i) (hnonneg i) hh hhr
  have he : -(n : ℝ)*(2*f i o/h^2+J*h/3) = -(b*f i o+a*h) := by
    dsimp [a,b]
    ring
  rw [he] at H
  linarith

end Yau.Proofs.C05GeometricNearMinimumAux

import Yau.Blueprint.HeatSmoothing

/-! The natural intermediate family produced by the heat construction.
All its clauses are actual values, local plateaux and derivative estimates. -/
noncomputable section
open Filter Set
open scoped Topology
namespace Yau.NodeProofs.P07Aux
open Yau Yau.Blueprint
variable {n : ℕ} {M : ComplexManifold n}

def ScaledCutoffFamily (g : SmoothMetric M) (o : M.Carrier)
    (v : ℝ → M.Carrier → ℝ) (D1 D2 : ℝ) : Prop :=
  ∀ L : ℝ, 0 < L → SmoothFn (v L) ∧ ∀ x,
    v L x ∈ Icc (0 : ℝ) 1 ∧
    (distFrom g.form o x ≤ L → v L =ᶠ[𝓝 x] fun _ => 0) ∧
    (2 * L ≤ distFrom g.form o x → v L =ᶠ[𝓝 x] fun _ => 1) ∧
    gradNormSq g.form (v L) x ≤ (D1 / L) ^ 2 ∧
    ∀ w : ComplexVector n, |leviDirection (levi (v L) x) w| ≤
      (D2 / L ^ 2) * leviDirection (gMat g.form x) w

theorem scaledCutoff_zero {g : SmoothMetric M} {o : M.Carrier}
    {v : ℝ → M.Carrier → ℝ} {D1 D2 L : ℝ} (hv : ScaledCutoffFamily g o v D1 D2)
    (hL : 0 < L) (x : M.Carrier) (hx : distFrom g.form o x ≤ L) : v L x = 0 :=
  ((hv L hL).2 x).2.1 hx |>.eq_of_nhds

theorem scaledCutoff_one {g : SmoothMetric M} {o : M.Carrier}
    {v : ℝ → M.Carrier → ℝ} {D1 D2 L : ℝ} (hv : ScaledCutoffFamily g o v D1 D2)
    (hL : 0 < L) (x : M.Carrier) (hx : 2 * L ≤ distFrom g.form o x) : v L x = 1 :=
  ((hv L hL).2 x).2.2.1 hx |>.eq_of_nhds

end Yau.NodeProofs.P07Aux

import Yau.Proofs.P07ProfilesScalar
import Yau.Proofs.P06Geometry
import Mathlib.Analysis.Calculus.MeanValue

/-! The fixed distance truncations: all basic data except the separate
geometric weak Levi estimate. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff NNReal
namespace Yau.NodeProofs.P07Aux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

def radialTruncation (g : SmoothMetric M) (o : M.Carrier) (L : ℝ) (x : M.Carrier) : ℝ :=
  radialProfile (distFrom g.form o x ^ 2 / L ^ 2)

theorem radialTruncation_mem (g : SmoothMetric M) (o : M.Carrier) (L : ℝ) (x : M.Carrier) :
    radialTruncation g o L x ∈ Icc (0 : ℝ) 1 := radialProfile_mem _

theorem radialTruncation_continuous (g : SmoothMetric M) (o : M.Carrier) (L : ℝ) :
    Continuous (radialTruncation g o L) :=
  radialProfile_contDiff.continuous.comp ((continuous_distFrom g o).pow 2 |>.div_const (L ^ 2))

theorem radialTruncation_zero (g : SmoothMetric M) (o : M.Carrier) {L : ℝ} (hL : 0 < L)
    (x : M.Carrier) (hx : distFrom g.form o x ≤ L) : radialTruncation g o L x = 0 := by
  apply radialProfile_zero
  apply (div_le_one (sq_pos_of_pos hL)).mpr
  have hd : 0 ≤ distFrom g.form o x := g.induced_distance_nonneg o x
  nlinarith

theorem radialTruncation_one (g : SmoothMetric M) (o : M.Carrier) {L : ℝ} (hL : 0 < L)
    (x : M.Carrier) (hx : 2 * L ≤ distFrom g.form o x) : radialTruncation g o L x = 1 := by
  apply radialProfile_one
  apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
  nlinarith

theorem radialTruncation_compactExterior (g : SmoothMetric M) (o : M.Carrier)
    {L : ℝ} (hL : 0 < L) :
    ∃ K : Set M.Carrier, IsCompact K ∧ ∀ x, x ∉ K → radialTruncation g o L x = 1 := by
  refine ⟨{x | distFrom g.form o x ≤ 2 * L}, isCompact_inducedDistance_sublevel g o (2 * L), ?_⟩
  intro x hx
  exact radialTruncation_one g o hL x (le_of_lt (lt_of_not_ge hx))

theorem radialScalar_deriv {L : ℝ} (hL : 0 < L) (s : ℝ) :
    deriv (fun r : ℝ => radialProfile (r ^ 2 / L ^ 2)) s =
      deriv radialProfile (s ^ 2 / L ^ 2) * (2 * s / L ^ 2) := by
  have hd : HasDerivAt (fun r : ℝ => r ^ 2 / L ^ 2) (2 * s / L ^ 2) s := by
    convert ((hasDerivAt_id s).pow 2).div_const (L ^ 2) using 1 <;> simp
  exact ((radialProfile_contDiff.differentiable (by simp) (s ^ 2 / L ^ 2)).hasDerivAt.comp s hd).deriv

theorem radialScalar_deriv_bound {A1 L : ℝ} (hA1 : 0 < A1) (hL : 0 < L)
    (hA : ∀ s, |deriv radialProfile s| ≤ A1) (s : ℝ) :
    |deriv (fun r : ℝ => radialProfile (r ^ 2 / L ^ 2)) s| ≤ 4 * A1 / L := by
  rw [radialScalar_deriv hL s, abs_mul]
  by_cases hs : |s| ≤ 2 * L
  · have hrhs : (4 / L) * L ^ 2 = 4 * L := by field_simp
    have hratio : |2 * s / L ^ 2| ≤ 4 / L := by
      rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg (sq_nonneg L)]
      apply (div_le_iff₀ (sq_pos_of_pos hL)).mpr
      rw [hrhs]
      linarith
    calc
      _ ≤ A1 * (4 / L) := mul_le_mul (hA _) hratio (abs_nonneg _) hA1.le
      _ = _ := by ring
  · have harg : 4 < s ^ 2 / L ^ 2 := by
      apply (lt_div_iff₀ (sq_pos_of_pos hL)).mpr
      nlinarith [abs_nonneg s, sq_abs s]
    have heq : radialProfile =ᶠ[𝓝 (s ^ 2 / L ^ 2)] fun _ => 1 := by
      filter_upwards [Ioi_mem_nhds harg] with y hy
      exact radialProfile_one y hy.le
    rw [(derivs_zero_of_locally_constant heq).1, abs_zero, zero_mul]
    positivity

theorem radialTruncation_lipschitz_bound (g : SmoothMetric M) (o : M.Carrier)
    {A1 L : ℝ} (hA1 : 0 < A1) (hL : 0 < L)
    (hA : ∀ s, |deriv radialProfile s| ≤ A1) :
    ∀ x y, |radialTruncation g o L x - radialTruncation g o L y| ≤
      (4 * A1 / L) * inducedDistance g.form x y := by
  let B : NNReal := ⟨4 * A1 / L, by positivity⟩
  have hf : Differentiable ℝ (fun r : ℝ => radialProfile (r ^ 2 / L ^ 2)) :=
    (radialProfile_contDiff.comp ((contDiff_id.pow 2).div_const (L ^ 2))).differentiable (by simp)
  have hLip : LipschitzWith B (fun r : ℝ => radialProfile (r ^ 2 / L ^ 2)) := by
    apply lipschitzWith_of_nnnorm_deriv_le hf
    intro s
    exact_mod_cast radialScalar_deriv_bound hA1 hL hA s
  intro x y
  have he := hLip.dist_le_mul (distFrom g.form o x) (distFrom g.form o y)
  rw [Real.dist_eq, Real.dist_eq] at he
  exact he.trans (mul_le_mul_of_nonneg_left (abs_distFrom_sub_le g o x y) B.coe_nonneg)

end Yau.NodeProofs.P07Aux

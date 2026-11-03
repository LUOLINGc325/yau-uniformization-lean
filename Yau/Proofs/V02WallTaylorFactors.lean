import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Compactness.Compact

/-! Polynomial clearing of reciprocal walls and a compact uniform smallness lemma. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof

/-- The wall ratio multiplier extends smoothly through a vanishing wall. -/
def wallRatioMultiplier (a : ℕ) (u v : ℝ) : ℝ := u ^ (a - 1) * v ^ a

/-- The reciprocal difference multiplier also extends through a vanishing wall. -/
def wallInverseMultiplier (a : ℕ) (u v : ℝ) : ℝ := u ^ (a - 2) * v ^ a

theorem wallPower_eq_mul_ratio {a : ℕ} (ha : 1 ≤ a) (u v : ℝ) :
    (u * v) ^ a = u * wallRatioMultiplier a u v := by
  dsimp [wallRatioMultiplier]
  rw [mul_pow, ← mul_assoc, ← pow_succ']
  congr 2
  omega

theorem wallPower_eq_sq_mul_inverse {a : ℕ} (ha : 2 ≤ a) (u v : ℝ) :
    (u * v) ^ a = u ^ 2 * wallInverseMultiplier a u v := by
  dsimp [wallInverseMultiplier]
  rw [mul_pow, ← mul_assoc, ← pow_add]
  congr 2
  omega

theorem wall_factorization {a : ℕ} (ha : 1 ≤ a) (u v R : ℝ) :
    u + (u * v) ^ a * R = u * (1 + wallRatioMultiplier a u v * R) := by
  rw [wallPower_eq_mul_ratio ha]
  ring

theorem wallRatioMultiplier_mem_Icc {a : ℕ} {u v : ℝ}
    (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1) :
    wallRatioMultiplier a u v ∈ Set.Icc 0 1 := by
  exact ⟨mul_nonneg (pow_nonneg hu.1 _) (pow_nonneg hv.1 _),
    mul_le_one₀ (pow_le_one₀ hu.1 hu.2) (pow_nonneg hv.1 _) (pow_le_one₀ hv.1 hv.2)⟩

theorem wall_ratio_bounds {a : ℕ} {u v R : ℝ}
    (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1) (hR : |R| ≤ 1 / 2) :
    1 / 2 ≤ 1 + wallRatioMultiplier a u v * R ∧
      1 + wallRatioMultiplier a u v * R ≤ 3 / 2 := by
  have hs := wallRatioMultiplier_mem_Icc (a := a) hu hv
  have hb : |wallRatioMultiplier a u v * R| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_nonneg hs.1]
    exact (mul_le_mul_of_nonneg_left hR hs.1).trans (by nlinarith [hs.2])
  have hh := abs_le.mp hb
  constructor <;> linarith

theorem wall_factor_positive {a : ℕ} (ha : 1 ≤ a) {u v R : ℝ}
    (hu : 0 < u) (hu1 : u ≤ 1) (hv : v ∈ Set.Icc 0 1) (hR : |R| ≤ 1 / 2) :
    0 < u + (u * v) ^ a * R := by
  rw [wall_factorization ha]
  exact mul_pos hu (lt_of_lt_of_le (by norm_num) (wall_ratio_bounds ⟨hu.le, hu1⟩ hv hR).1)

theorem reciprocal_wall_difference {a : ℕ} (ha : 2 ≤ a) {u v R : ℝ}
    (hu : u ≠ 0) (hfactor : 1 + wallRatioMultiplier a u v * R ≠ 0) :
    (u + (u * v) ^ a * R)⁻¹ - u⁻¹ =
      -(wallInverseMultiplier a u v * R) / (1 + wallRatioMultiplier a u v * R) := by
  have hs : wallRatioMultiplier a u v = u * wallInverseMultiplier a u v := by
    dsimp [wallRatioMultiplier, wallInverseMultiplier]
    rw [← mul_assoc, ← pow_succ']
    congr 2
    omega
  rw [wall_factorization (by omega : 1 ≤ a), hs]
  rw [hs] at hfactor
  field_simp [hu, hfactor]
  <;> ring

theorem log_wall_difference {a : ℕ} (ha : 1 ≤ a) {u v R : ℝ}
    (hu : u ≠ 0) (hfactor : 1 + wallRatioMultiplier a u v * R ≠ 0) :
    Real.log (u + (u * v) ^ a * R) - Real.log u =
      Real.log (1 + wallRatioMultiplier a u v * R) := by
  rw [wall_factorization ha, Real.log_mul hu hfactor]
  ring

theorem wallInverseMultiplier_contDiff (a : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => wallInverseMultiplier a p.1 p.2) :=
  (contDiff_fst.pow _).mul (contDiff_snd.pow _)

theorem wallRatioMultiplier_contDiff (a : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => wallRatioMultiplier a p.1 p.2) :=
  (contDiff_fst.pow _).mul (contDiff_snd.pow _)

/-- Compactness supplies one parameter radius; no positive lower bound on either wall is used. -/
theorem exists_uniform_small_factor {P : Type*} [TopologicalSpace P]
    {K : Set P} (hK : IsCompact K) {Ω : Set (ℂ × P)} (hΩ : IsOpen Ω)
    {R : ℂ × P → ℝ} (hR : ContinuousOn R Ω)
    (hzero : ∀ p ∈ K, (0, p) ∈ Ω ∧ R (0, p) = 0)
    {S : ℝ} (hS : 0 < S) :
    ∃ r : ℝ, 0 < r ∧ r < S ∧ ∀ z ∈ Metric.ball 0 r, ∀ p ∈ K,
      (z, p) ∈ Ω ∧ |R (z, p)| < 1 / 2 := by
  let W : Set (ℂ × P) := Ω ∩ R ⁻¹' Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)
  have hW : IsOpen W := hR.isOpen_inter_preimage hΩ isOpen_Ioo
  have hsub : ({0} : Set ℂ) ×ˢ K ⊆ W := by
    rintro ⟨z, p⟩ ⟨hz, hp⟩
    have hz0 : z = 0 := hz
    subst z
    rcases hzero p hp with ⟨hpΩ, hpR⟩
    exact ⟨hpΩ, by simp [hpR]⟩
  obtain ⟨A, B, hA, _, h0A, hKB, hAB⟩ :=
    generalized_tube_lemma isCompact_singleton hK hW hsub
  obtain ⟨ε, hε, hεA⟩ := Metric.isOpen_iff.mp hA 0 (h0A (by simp))
  refine ⟨min ε S / 2, by positivity, ?_, ?_⟩
  · have := min_le_right ε S
    linarith [lt_min hε hS]
  intro z hz p hp
  have hεz : z ∈ Metric.ball 0 ε :=
    Metric.ball_subset_ball (by linarith [min_le_left ε S, lt_min hε hS]) hz
  have hh := hAB (show (z, p) ∈ A ×ˢ B from ⟨hεA hεz, hKB hp⟩)
  exact ⟨hh.1, abs_lt.mpr hh.2⟩

end Yau.Blueprint.V02WallTaylorProof

import Yau.Proofs.F04CovectorMatrix

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

def massProfile (s : ℝ) : ℝ := 1 - Real.smoothTransition (s - 1)

theorem massProfile_smooth : ContDiff ℝ ∞ massProfile :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))

theorem massProfile_range (s : ℝ) : 0 ≤ massProfile s ∧ massProfile s ≤ 1 := by
  have h0 := Real.smoothTransition.nonneg (s - 1)
  have h1 := Real.smoothTransition.le_one (s - 1)
  dsimp only [massProfile]
  constructor <;> linarith

theorem massProfile_one {s : ℝ} (hs : s ≤ 1) : massProfile s = 1 := by
  rw [massProfile, Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]

theorem massProfile_zero {s : ℝ} (hs : 2 ≤ s) : massProfile s = 0 := by
  rw [massProfile, Real.smoothTransition.one_of_one_le (by linarith), sub_self]

theorem massProfile_antitone : Antitone massProfile := by
  intro s t hst
  have hh := Real.smoothTransition.monotone (show s - 1 ≤ t - 1 by linarith)
  dsimp only [massProfile]
  linarith

theorem massProfile_one_germ {s : ℝ} (hs : s < 1) :
    massProfile =ᶠ[𝓝 s] (fun _ => (1 : ℝ)) := by
  filter_upwards [Iio_mem_nhds hs] with t ht
  exact massProfile_one (show t ≤ 1 from ht.le)

theorem massProfile_zero_germ {s : ℝ} (hs : 2 < s) :
    massProfile =ᶠ[𝓝 s] (fun _ => (0 : ℝ)) := by
  filter_upwards [Ioi_mem_nhds hs] with t ht
  exact massProfile_zero (show 2 ≤ t from ht.le)

theorem massProfile_deriv_compact : HasCompactSupport (deriv massProfile) := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Icc (1 : ℝ) 2) isCompact_Icc
  intro s hs
  by_contra hsmem
  have hcase : s < 1 ∨ 2 < s := by
    by_cases hs1 : 1 ≤ s
    · exact Or.inr (lt_of_not_ge (fun hs2 => hsmem ⟨hs1, hs2⟩))
    · exact Or.inl (lt_of_not_ge hs1)
  have hd : deriv massProfile s = 0 := by
    rcases hcase with h | h
    · rw [(massProfile_one_germ h).deriv_eq]
      exact deriv_const s 1
    · rw [(massProfile_zero_germ h).deriv_eq]
      exact deriv_const s 0
  exact hs hd

theorem massProfile_derivative_bounds :
    ∃ B : ℝ, 0 < B ∧ ∀ s : ℝ, |deriv massProfile s| ≤ B ∧ |deriv (deriv massProfile) s| ≤ B := by
  have hd : ContDiff ℝ ∞ (deriv massProfile) := (contDiff_infty_iff_deriv.mp massProfile_smooth).2
  have hdd : ContDiff ℝ ∞ (deriv (deriv massProfile)) := (contDiff_infty_iff_deriv.mp hd).2
  obtain ⟨B₁, hB₁⟩ := (massProfile_deriv_compact.norm.isCompact_range hd.continuous.norm).bddAbove
  obtain ⟨B₂, hB₂⟩ := (massProfile_deriv_compact.deriv.norm.isCompact_range hdd.continuous.norm).bddAbove
  refine ⟨1 + |B₁| + |B₂|, by positivity, ?_⟩
  intro s
  have hb₁ := hB₁ (mem_range_self s)
  have hb₂ := hB₂ (mem_range_self s)
  simp only [Real.norm_eq_abs] at hb₁ hb₂
  constructor <;> nlinarith [le_abs_self B₁, le_abs_self B₂, abs_nonneg B₁, abs_nonneg B₂]

def massCutoff {α : Type*} (u : α → ℝ) (N : ℝ) (x : α) : ℝ := massProfile (u x / N)

theorem massCutoff_smooth {n : ℕ} {M : ComplexManifold n} {u : M.Carrier → ℝ}
    (hu : SmoothFn u) (N : ℝ) : SmoothFn (massCutoff u N) := by
  intro x
  exact massProfile_smooth.comp_contDiffOn ((hu x).div_const N)

theorem massCutoff_range {α : Type*} (u : α → ℝ) (N : ℝ) (x : α) :
    0 ≤ massCutoff u N x ∧ massCutoff u N x ≤ 1 := massProfile_range _

theorem massCutoff_one {α : Type*} (u : α → ℝ) {N : ℝ} (hN : 0 < N) {x : α}
    (hx : u x ≤ N) : massCutoff u N x = 1 :=
  massProfile_one ((div_le_one hN).mpr hx)

theorem massCutoff_zero {α : Type*} (u : α → ℝ) {N : ℝ} (hN : 0 < N) {x : α}
    (hx : 2 * N ≤ u x) : massCutoff u N x = 0 :=
  massProfile_zero ((le_div_iff₀ hN).mpr hx)

theorem massCutoff_mono {α : Type*} (u : α → ℝ) (hu : ∀ x, 0 ≤ u x)
    {N L : ℝ} (hN : 0 < N) (hNL : N ≤ L) (x : α) : massCutoff u N x ≤ massCutoff u L x := by
  exact massProfile_antitone (div_le_div_of_nonneg_left (hu x) hN hNL)

theorem massCutoff_tsupport_sublevel {n : ℕ} {M : ComplexManifold n} {u : M.Carrier → ℝ}
    (hu : SmoothFn u) {N : ℝ} (hN : 0 < N) :
    tsupport (massCutoff u N) ⊆ {x | u x ≤ 2 * N} := by
  apply closure_minimal _ (isClosed_le (LeafProofs.L18Aux.continuous_of_smoothFn hu) continuous_const)
  intro x hx
  by_contra h
  exact hx (massCutoff_zero u hN (le_of_not_ge h))

theorem massCutoff_compact {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) {N : ℝ} (hN : 0 < N) :
    HasCompactSupport (massCutoff u N) :=
  (hu.2.1 (2 * N)).of_isClosed_subset (isClosed_tsupport _) (massCutoff_tsupport_sublevel hu.1 hN)

end Yau.F04Proof

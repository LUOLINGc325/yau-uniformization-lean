import Yau.Proofs.V04ClockTaylorExpComposition
import Yau.Proofs.V04UniformCenters
import Mathlib.Topology.MetricSpace.Thickening

/-! A single compact neighborhood of the original centers supplies both
backward admissibility and the actual test's uniform Taylor remainder. -/
open Set
open scoped Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof.ClockTaylorAux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

theorem compact_logtime_taylor {O K : Set (E × ℝ)} (hO : IsOpen O) (hK : IsCompact K)
    (hKO : K ⊆ O) {f : E × ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f O) {T : ℝ} (hT : 0 < T) :
    ∃ r R : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 ≤ R ∧ ∀ p ∈ K, 0 < p.2 → p.2 ≤ T →
      ∀ u ∈ Icc (-r) 0, (p.1, p.2 * Real.exp u) ∈ O ∧
        |f (p.1, p.2 * Real.exp u) - f p -
          u * p.2 * deriv (fun t => f (p.1, t)) p.2| ≤ R * u ^ 2 := by
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_cthickening_subset_open hO hKO
  let Kp := Metric.cthickening δ K
  have hKp : IsCompact Kp := hK.cthickening (r := δ)
  let D₁ (p : E × ℝ) := fderiv ℝ f p (0, 1)
  let D₂ (p : E × ℝ) := fderiv ℝ D₁ p (0, 1)
  have hD₁ : ContDiffOn ℝ ∞ D₁ O :=
    (hf.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const
  have hD₂ : ContDiffOn ℝ ∞ D₂ O :=
    (hD₁.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const
  obtain ⟨M₁, hM₁⟩ := hKp.exists_bound_of_continuousOn (hD₁.continuousOn.mono hδO)
  obtain ⟨M₂, hM₂⟩ := hKp.exists_bound_of_continuousOn (hD₂.continuousOn.mono hδO)
  let M := max 0 M₁ + max 0 M₂
  have hM : 0 ≤ M := add_nonneg (le_max_left _ _) (le_max_left _ _)
  have hb (p : E × ℝ) (hp : p ∈ Kp) : |D₁ p| ≤ M ∧ |D₂ p| ≤ M := by
    have h₁ := hM₁ p hp
    have h₂ := hM₂ p hp
    rw [Real.norm_eq_abs] at h₁ h₂
    exact ⟨h₁.trans (by dsimp [M]; linarith [le_max_right 0 M₁, le_max_left 0 M₂]),
      h₂.trans (by dsimp [M]; linarith [le_max_right 0 M₂, le_max_left 0 M₁])⟩
  let r := min 1 (δ / (2 * (T + 1)))
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := min_le_left _ _
  have hTr : T * r < δ := by
    have hh := min_le_right (1 : ℝ) (δ / (2 * (T + 1)))
    have hm : 2 * (T + 1) * r ≤ δ := by
      simpa only [r, mul_comm] using (le_div_iff₀ (by positivity : 0 < 2 * (T + 1))).mp hh
    nlinarith
  have hnear (p : E × ℝ) (hp : p ∈ K) (hs : 0 < p.2) (hsT : p.2 ≤ T)
      (u : ℝ) (hu : u ∈ Icc (-r) 0) : (p.1, p.2 * Real.exp u) ∈ Kp := by
    apply Metric.mem_cthickening_of_dist_le _ p δ K hp
    rw [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg), Real.dist_eq]
    have he := Real.exp_le_one_iff.mpr hu.2
    rw [abs_of_nonpos (by nlinarith : p.2 * Real.exp u - p.2 ≤ 0)]
    have hexp := Real.add_one_le_exp u
    have hlin : p.2 - p.2 * Real.exp u ≤ p.2 * (-u) := by nlinarith
    have hh := hlin.trans ((mul_le_mul hsT (by linarith [hu.1]) (by linarith [hu.2]) hT.le).trans hTr.le)
    linarith
  have hslice (p : E × ℝ) (hp : p ∈ O) :
      HasDerivAt (fun t => f (p.1, t)) (D₁ p) p.2 := by
    exact ((hf.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  have hslice₁ (p : E × ℝ) (hp : p ∈ O) :
      HasDerivAt (fun t => D₁ (p.1, t)) (D₂ p) p.2 := by
    exact ((hD₁.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  refine ⟨r, M * T ^ 2 + M * T, hr, hr1, by positivity, ?_⟩
  intro p hp hs hsT u hu
  refine ⟨hδO (hnear p hp hs hsT u hu), ?_⟩
  have hh := exp_composition_taylor (f := fun t => f (p.1, t))
    (f₁ := fun t => D₁ (p.1, t)) (f₂ := fun t => D₂ (p.1, t))
    (r := r) (M := M) (t := p.2) (T := T) (γ := 1) (C := 1)
    hr hM hs.le hsT zero_le_one le_rfl (fun v hv => ?_) hu
  · rw [(hslice p (hKO hp)).deriv]
    simpa only [mul_one, one_pow, Prod.mk.eta, mul_assoc] using hh
  · have hp' := hnear p hp hs hsT v hv
    refine ⟨?_, ?_, ?_⟩
    · simpa only [mul_one] using hslice _ (hδO hp')
    · simpa only [mul_one] using hslice₁ _ (hδO hp')
    · simpa only [mul_one] using hb _ hp'

variable {n q : ℕ} {X : KahlerManifold n}

theorem compact_center_test_taylor {d : VariationData X q} (hd : VariationSetup d)
    {Kc : Set (CotangentCoord n × ℝ)} (hKc : IsCompact Kc)
    (hKcO : Kc ⊆ interior (centerCylinder d)) :
    ∃ r R : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 ≤ R ∧ ∀ F : VariationDisc X,
      InCotangentTimeChart d.chart (F.f 0) F.s Kc → 0 < F.s → F.s ≤ d.T →
      ∀ u ∈ Icc (-r) 0,
        InCotangentTimeChart d.chart (F.f 0) (F.s * Real.exp u) (interior (centerCylinder d)) ∧
        |d.test (F.f 0) (F.s * Real.exp u) - d.test (F.f 0) F.s -
          u * F.s * deriv (d.test (F.f 0)) F.s| ≤ R * u ^ 2 := by
  obtain ⟨V, hV, hCV, _, htest⟩ := hd.2.2.2.2.2.2.2.1.2.2.2.2.2.2
  have hf : ContDiffOn ℝ ∞ (contactTest d) (interior (centerCylinder d)) :=
    htest.mono (interior_subset.trans hCV)
  obtain ⟨r, R, hr, hr1, hR, hb⟩ := compact_logtime_taylor isOpen_interior hKc hKcO hf hd.1
  refine ⟨r, R, hr, hr1, hR, fun F hc hs hsT u hu => ?_⟩
  have hh := hb (cotangentChart d.chart (F.f 0), F.s) hc.2 hs hsT u hu
  refine ⟨⟨hc.1, hh.1⟩, ?_⟩
  simpa only [contactTest, cotangentChart_left_inv d.chart hc.1] using hh.2

end Yau.Blueprint.V04Proof.ClockTaylorAux

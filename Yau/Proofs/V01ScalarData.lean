import Yau.Proofs.V01TailWall

/-! The scalar localization data come from the same supplied localized flow
and its original scalar-comparison conclusion, on the larger horizon T+1. -/

noncomputable section
open Set Filter
open scoped Topology
namespace Yau.Blueprint.V01Proof
variable {n : ℕ} {X : KahlerManifold n}

theorem exists_scalar_localization_data
    (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (hComp : ScalarComparison X h ρ)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) (T : ℝ) (hT : 0 < T) :
    ∃ (Q : STF X) (ρs : ℕ → STF X) (A : ℕ → ℝ),
      SmoothSpaceTime Q (Icc 0 (T + 1)) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ x t, t ∈ Icc 0 (T + 1) →
        c * (1 + distFrom X.metric.form o x ^ 2) ≤ Q x t ∧
        c * traceWith (gMat (h t) x) (gMat X.metric.form x) ≤
          heatOp h (Icc 0 (T + 1)) Q x t) ∧
      (∀ j, SmoothSpaceTime (ρs j) (Icc 0 (T + 1)) ∧
        ∃ C : ℝ, ∀ x t, t ∈ Icc 0 (T + 1) →
          0 ≤ ρs j x t ∧ ρs j x t ≤ ρ x t ∧ ρ x t - C ≤ ρs j x t ∧
            0 ≤ heatOp h (Icc 0 (T + 1)) (ρs j) x t) ∧
      (∀ K : Set (Pt X), IsCompact K → ∀ ε, 0 < ε → ∀ᶠ j in atTop,
        ∀ x ∈ K, ∀ t ∈ Icc 0 (T + 1), ρs j x t ≤ ε) ∧
      StrictMono A ∧ Tendsto A atTop atTop ∧
      ∀ j, 0 < A j ∧ ∀ x t, t ∈ Icc 0 T → A j / 3 < u x →
        ρ x t + ((j : ℝ) + 1) ≤ ((j : ℝ) + 1)⁻¹ * Q x t + ρs j x t := by
  have hExt : 0 < T + 1 := by linarith
  have hQexists := hloc
  rcases hQexists with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hQexists⟩
  obtain ⟨Q, c, hc, hQSmooth, hQ⟩ := hQexists (T + 1) hExt
  obtain ⟨ρs, Cs, hTail, hSmall⟩ := (hComp (T + 1) hExt).2.2.1
  obtain ⟨Cu, hCu, hU⟩ := hu.2.2.2
  let b : ℕ → ℝ := fun j =>
    3 * Cu * (2 + ((j : ℝ) + 1) * (max (Cs j) 0 + ((j : ℝ) + 1)) / c)
  let A := increasingBound b
  refine ⟨Q, ρs, A, hQSmooth, ⟨c, hc, fun x t ht => (hQ x t ht).2⟩,
    (fun j => ⟨(hTail j).1, Cs j, (hTail j).2⟩), ?_,
    increasingBound_strictMono b, increasingBound_tendsto_atTop b, ?_⟩
  · intro K hK ε hε
    obtain ⟨J, hJ⟩ := hSmall K hK ε hε
    exact eventually_atTop.2 ⟨J, hJ⟩
  · intro j
    refine ⟨increasingBound_pos b j, ?_⟩
    intro x t ht hAway
    have htExt : t ∈ Icc 0 (T + 1) := ⟨ht.1, by linarith [ht.2]⟩
    exact tail_wall_scalar_bound (distFrom X.metric.form o x) (u x) (A j)
      (Q x t) (ρ x t) (ρs j x t) Cu c (Cs j) ((j : ℝ) + 1)
      hCu hc (by positivity) (hU x).2.1 (increasingBound_ge b j) hAway
      (hQ x t htExt).2.1 ((hTail j).2 x t htExt).2.2.1

end Yau.Blueprint.V01Proof

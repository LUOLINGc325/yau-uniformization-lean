import Yau.Proofs.C07LocalInversion

open scoped Topology

noncomputable section

namespace Yau.Proofs.C07ShortLiftAux

open Set Filter

section TopologicalContinuation

variable {E X : Type*} [MetricSpace E] [TopologicalSpace X] [T2Space X]
  {p : E → X} {U K : Set E} {γ : ℝ → X}

/-- On a compact set of possible lifted positions, the local inverse
branches admit one positive time step for a fixed continuous base path. -/
theorem uniform_inverse_time_step
    (hK : IsCompact K) (hKU : K ⊆ U) (hp : ContinuousOn p U)
    (hloc : ∀ z ∈ U, ∃ e : OpenPartialHomeomorph E X,
      z ∈ e.source ∧ e.source ⊆ U ∧ EqOn e p e.source)
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1)) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ K, p z = γ t →
      ∃ e : OpenPartialHomeomorph E X,
        z ∈ e.source ∧ e.source ⊆ U ∧ EqOn e p e.source ∧
        ∀ s ∈ Icc (0 : ℝ) 1, |s - t| < δ → γ s ∈ e.target := by
  classical
  let J := Icc (0 : ℝ) 1
  let D := K
  letI : CompactSpace D := isCompact_iff_compactSpace.mp hK
  have hpD : Continuous (fun z : D => p z) :=
    continuousOn_iff_continuous_restrict.mp (hp.mono hKU)
  have hγJ : Continuous (fun t : J => γ t) :=
    continuousOn_iff_continuous_restrict.mp hγ
  let T : Set (J × D) := {q | p q.2 = γ q.1}
  have hT : IsCompact T :=
    (isClosed_eq (hpD.comp continuous_snd) (hγJ.comp continuous_fst)).isCompact
  choose e he using fun q : T => hloc q.1.2 (hKU q.1.2.2)
  let V : T → Set (J × D) := fun q =>
    ((fun t : J => γ t) ⁻¹' (e q).target) ×ˢ
      ((fun z : D => (z : E)) ⁻¹' (e q).source)
  have hVo : ∀ q, IsOpen (V q) := fun q =>
    (hγJ.isOpen_preimage _ (e q).open_target).prod
      (continuous_subtype_val.isOpen_preimage _ (e q).open_source)
  have hcover : T ⊆ ⋃ q, V q := by
    intro q hq
    refine mem_iUnion.mpr ⟨⟨q, hq⟩, ?_⟩
    refine ⟨?_, (he ⟨q, hq⟩).1⟩
    change γ q.1 ∈ (e ⟨q, hq⟩).target
    rw [← hq, ← (he ⟨q, hq⟩).2.2 (he ⟨q, hq⟩).1]
    exact (e ⟨q, hq⟩).map_source (he ⟨q, hq⟩).1
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric hT hVo hcover
  refine ⟨δ, hδ, ?_⟩
  intro t ht z hz hzt
  let q : J × D := (⟨t, ht⟩, ⟨z, hz⟩)
  have hq : q ∈ T := hzt
  obtain ⟨i, hi⟩ := hball q hq
  have hqi := hi (Metric.mem_ball_self hδ)
  refine ⟨e i, hqi.2, (he i).2.1, (he i).2.2, ?_⟩
  intro s hs hst
  have hdist : dist ((⟨s, hs⟩ : J), (⟨z, hz⟩ : D)) q < δ := by
    simpa only [q, Prod.dist_eq, Subtype.dist_eq, dist_self,
      Real.dist_eq] using max_lt hst hδ
  exact (hi hdist).1

/-- A continuous lift confined a priori to a compact subset of the local
homeomorphism domain can be extended across the entire unit interval.
The confinement condition is used only after an actual partial lift has
been constructed. -/
theorem exists_lift_of_compact_confinement
    {z₀ : E} (hz₀ : z₀ ∈ U) (hpz₀ : p z₀ = γ 0)
    (hK : IsCompact K) (hKU : K ⊆ U) (hp : ContinuousOn p U)
    (hloc : ∀ z ∈ U, ∃ e : OpenPartialHomeomorph E X,
      z ∈ e.source ∧ e.source ⊆ U ∧ EqOn e p e.source)
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hconf : ∀ b ∈ Icc (0 : ℝ) 1, ∀ η : ℝ → E,
      ContinuousOn η (Icc 0 b) → η 0 = z₀ →
      (∀ t ∈ Icc 0 b, η t ∈ U ∧ p (η t) = γ t) →
      ∀ t ∈ Icc 0 b, η t ∈ K) :
    ∃ η : ℝ → E, ContinuousOn η (Icc (0 : ℝ) 1) ∧ η 0 = z₀ ∧
      ∀ t ∈ Icc (0 : ℝ) 1, η t ∈ U ∧ p (η t) = γ t := by
  classical
  obtain ⟨δ, hδ, hstep⟩ := uniform_inverse_time_step hK hKU hp hloc hγ
  let τ : ℕ → ℝ := fun j => min ((j : ℝ) * (δ / 2)) 1
  have hτ (j : ℕ) : τ j ∈ Icc (0 : ℝ) 1 :=
    ⟨le_min (by positivity) zero_le_one, min_le_right _ _⟩
  have hτmono (j : ℕ) : τ j ≤ τ (j + 1) := by
    dsimp [τ]
    apply min_le_min_right
    push_cast
    nlinarith
  have hτstep (j : ℕ) : τ (j + 1) - τ j < δ := by
    dsimp [τ]
    by_cases hj : (j : ℝ) * (δ / 2) ≤ 1
    · rw [min_eq_left hj]
      have hmin := min_le_left (((j + 1 : ℕ) : ℝ) * (δ / 2)) (1 : ℝ)
      push_cast at hmin
      push_cast
      linarith
    · rw [min_eq_right (le_of_not_ge hj)]
      have hmin := min_le_right (((j + 1 : ℕ) : ℝ) * (δ / 2)) (1 : ℝ)
      linarith
  have hex (j : ℕ) : ∃ η : ℝ → E,
      ContinuousOn η (Icc 0 (τ j)) ∧ η 0 = z₀ ∧
      ∀ t ∈ Icc 0 (τ j), η t ∈ U ∧ p (η t) = γ t := by
    induction j with
    | zero =>
        refine ⟨fun _ => z₀, continuousOn_const, rfl, ?_⟩
        intro t ht
        have ht0 : t = 0 := by simpa [τ] using ht
        simpa only [ht0] using And.intro hz₀ hpz₀
    | succ j ih =>
        obtain ⟨η, hη, hη₀, hηp⟩ := ih
        have hηK := hconf (τ j) (hτ j) η hη hη₀ hηp
        have htj : τ j ∈ Icc (0 : ℝ) (τ j) := ⟨(hτ j).1, le_rfl⟩
        obtain ⟨e, hez, heU, hep, heγ⟩ :=
          hstep (τ j) (hτ j) (η (τ j)) (hηK _ htj) (hηp _ htj).2
        have hγe (s : ℝ) (hs : s ∈ Icc (τ j) (τ (j + 1))) : γ s ∈ e.target := by
          apply heγ s ⟨(hτ j).1.trans hs.1, hs.2.trans (hτ (j + 1)).2⟩
          rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
          exact (sub_le_sub_right hs.2 _).trans_lt (hτstep j)
        have heη : e.symm (γ (τ j)) = η (τ j) := by
          rw [← (hηp _ htj).2, ← hep hez]
          exact e.left_inv hez
        let η' : ℝ → E := fun s => if s ≤ τ j then η s else e.symm (γ s)
        have hη'₁ : ContinuousOn η' (Icc 0 (τ j)) := hη.congr fun s hs =>
          by simp only [η', if_pos hs.2]
        have hη'₂ : ContinuousOn η' (Icc (τ j) (τ (j + 1))) := by
          apply (e.continuousOn_symm.comp
            (hγ.mono (Icc_subset_Icc (hτ j).1 (hτ (j + 1)).2)) hγe).congr
          intro s hs
          dsimp [η']
          split_ifs with hs'
          · have hsj : s = τ j := le_antisymm hs' hs.1
            simpa only [hsj] using heη.symm
          · rfl
        refine ⟨η', ?_, ?_, ?_⟩
        · apply (hη'₁.union_of_isClosed hη'₂ isClosed_Icc isClosed_Icc).mono
          intro s hs
          by_cases hsj : s ≤ τ j
          · exact Or.inl ⟨hs.1, hsj⟩
          · exact Or.inr ⟨le_of_not_ge hsj, hs.2⟩
        · simpa only [η', if_pos (hτ j).1] using hη₀
        · intro s hs
          dsimp [η']
          split_ifs with hsj
          · exact hηp s ⟨hs.1, hsj⟩
          · have hes : γ s ∈ e.target := hγe s ⟨le_of_not_ge hsj, hs.2⟩
            exact ⟨heU (e.map_target hes), (hep (e.map_target hes)).symm.trans (e.right_inv hes)⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / δ)
  have hτN : τ N = 1 := by
    apply min_eq_right
    have hN' := (div_lt_iff₀ hδ).mp hN
    nlinarith
  simpa only [hτN] using hex N

end TopologicalContinuation

end Yau.Proofs.C07ShortLiftAux

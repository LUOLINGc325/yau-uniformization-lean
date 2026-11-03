import Yau.Proofs.D04GlueTools

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace Yau.Proofs.D04Aux

open Yau Yau.Blueprint

variable {n : ℕ}

/-- Compatible limits on a nested open exhaustion glue to the complete
frozen coordinate-domain L¹ alternative for the same input sequence. -/
theorem pshL1Limit_of_nested_local_limits
    {D : Set (ComplexVector n)} (hD : IsOpen D) (hne : D.Nonempty)
    (O : ℕ → Set (ComplexVector n))
    (hO : ∀ m, IsOpen (O m) ∧ O m ⊆ D) (hmono : Monotone O)
    (hcover : ∀ K : Set (ComplexVector n), IsCompact K → K ⊆ D → ∃ m, K ⊆ O m)
    (us : ℕ → ComplexVector n → EReal) (v : ℕ → ComplexVector n → EReal)
    (hvpsh : ∀ m, IsPshOn (v m) (O m))
    (hvL1 : ∀ m, CoordinateLocallyL1 (O m) (v m))
    (hinput : ∀ K : Set (ComplexVector n), IsCompact K → K ⊆ D →
      ∃ N : ℕ, ∀ j, N ≤ j → IntegrableOn (fun y => (us j y).toReal) K volume)
    (hreal : ∀ m K, IsCompact K → K ⊆ O m →
      Tendsto (fun j => ∫ y in K, |(us j y).toReal - (v m y).toReal|) atTop (𝓝 0))
    (hdist : ∀ m K, IsCompact K → K ⊆ O m →
      Tendsto (fun j => ∫⁻ y in K, erealDist (us j y) (v m y)) atTop (𝓝 0))
    (hhartogs : ∀ (m : ℕ) (c : ℝ), (∀ y ∈ O m, v m y = (c : EReal)) →
      ∀ K, IsCompact K → K ⊆ O m → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ j in atTop, ∀ y ∈ K, us j y ≤ ((c + ε : ℝ) : EReal)) :
    PshL1Limit D us id := by
  classical
  have hcompat (i j : ℕ) (hij : i ≤ j) : EqOn (v i) (v j) (O i) := by
    apply psh_eq_of_locally_ae_eq (hO i).1 (hvpsh i) (isPshOn_mono (hvpsh j) (hmono hij))
    intro K hK hKO
    exact finite_L1_limits_unique_of_eventually_integrable (hinput K hK (hKO.trans (hO i).2))
      (hvL1 i K hK hKO) (hvL1 j K hK (hKO.trans (hmono hij)))
      (hreal i K hK hKO) (hreal j K hK (hKO.trans (hmono hij)))
  have hmem (x : ComplexVector n) (hx : x ∈ D) : ∃ m, x ∈ O m := by
    obtain ⟨m, hm⟩ := hcover {x} isCompact_singleton (singleton_subset_iff.mpr hx)
    exact ⟨m, hm (mem_singleton x)⟩
  let idx : D → ℕ := fun x => Nat.find (hmem x x.2)
  let w : ComplexVector n → EReal := fun x => if hx : x ∈ D then v (idx ⟨x, hx⟩) x else 0
  have hweq (m : ℕ) : EqOn w (v m) (O m) := by
    intro x hx
    have hxD := (hO m).2 hx
    have hidx : idx ⟨x, hxD⟩ ≤ m := Nat.find_min' (hmem x hxD) hx
    have hxidx : x ∈ O (idx ⟨x, hxD⟩) := Nat.find_spec (hmem x hxD)
    change (if hx : x ∈ D then v (idx ⟨x, hx⟩) x else 0) = v m x
    rw [dite_eq_left hxD]
    exact hcompat _ m hidx hxidx
  have hwpshLocal (m : ℕ) : IsPshOn w (O m) :=
    isPshOn_congr (hvpsh m) (fun _ hx => (hweq m hx).symm)
  have hwpsh : IsPshOn w D := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨m, hm⟩ := hmem x hx
      exact (hwpshLocal m).1 x hm
    · intro x hx
      obtain ⟨m, hm⟩ := hmem x hx
      have hAt : UpperSemicontinuousAt (v m) x := by
        intro a ha
        have h := (hvpsh m).2.1 x hm a ha
        simpa only [(hO m).1.nhdsWithin_eq hm] using h
      apply UpperSemicontinuousWithinAt.congr_of_eventuallyEq
        (hAt.upperSemicontinuousWithinAt D) hx
      have heq : ∀ᶠ y in 𝓝 x, v m y = w y :=
        Filter.Eventually.mono ((hO m).1.mem_nhds hm) (fun _ hy => (hweq m hy).symm)
      exact heq.filter_mono nhdsWithin_le_nhds
    · intro z a hdisc φ hφ hmajor
      let K : Set (ComplexVector n) := (fun ζ : ℂ => z + ζ • a) '' Metric.closedBall 0 1
      have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) 1).image (by fun_prop)
      have hKD : K ⊆ D := by
        rintro y ⟨ζ, hζ, rfl⟩
        exact hdisc ζ (by simpa only [Metric.mem_closedBall, dist_zero_right] using hζ)
      obtain ⟨m, hm⟩ := hcover K hK hKD
      apply (hwpshLocal m).2.2 z a
        (fun ζ hζ => hm ⟨ζ, by simpa only [Metric.mem_closedBall, dist_zero_right] using hζ, rfl⟩)
        φ hφ hmajor
  have hfinite (K : Set (ComplexVector n)) (hK : IsCompact K) (hKD : K ⊆ D) :
      ∀ᵐ y ∂volume.restrict K, w y ≠ ⊥ ∧ w y ≠ ⊤ := by
    obtain ⟨m, hm⟩ := hcover K hK hKD
    filter_upwards [(hvL1 m K hK hm).1, ae_restrict_mem hK.measurableSet] with y hy hyK
    rw [hweq m (hm hyK)]
    exact hy
  have hfiniteD := ae_on_open_of_ae_on_compacts hD hfinite
  have hpoint : ∃ x ∈ D, w x ≠ ⊥ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae (hD.measure_pos volume hne).ne'
      (hfiniteD.mono fun _ hx => hx.1)
  unfold PshL1Limit
  simp only [Yau.LeafProofs.lebesgueC_eq_volume]
  refine ⟨w, hwpsh, hpoint, hfiniteD.mono (fun _ hx => hx.1), ?_, ?_⟩
  · intro K hKD hK
    obtain ⟨m, hm⟩ := hcover K hK hKD
    have heq : w =ᵐ[volume.restrict K] v m :=
      (ae_restrict_mem hK.measurableSet).mono fun _ hy => hweq m (hm hy)
    refine ⟨((hvL1 m K hK hm).2).congr ?_, ?_⟩
    · exact heq.symm.fun_comp EReal.toReal
    · apply (hdist m K hK hm).congr'
      apply Filter.Eventually.of_forall
      intro j
      apply lintegral_congr_ae
      filter_upwards [heq] with y hy
      simp only [id_eq, hy]
  · intro c hc K hKD hK ε hε
    obtain ⟨m, hm⟩ := hcover K hK hKD
    have hcm : ∀ y ∈ O m, v m y = (c : EReal) :=
      fun y hy => (hweq m hy).symm.trans (hc y ((hO m).2 hy))
    exact eventually_atTop.mp (hhartogs m c hcm K hK hm ε hε)

end Yau.Proofs.D04Aux

import spec.CHAIN.LeafObligations

noncomputable section

open Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem spatial_jets_zero_of_slice {n : ℕ} {O : Set (Space n)} {u : Point n → ℝ}
    (hO : IsOpen O) {x : Space n} (hx : x ∈ O) {t : ℝ}
    (hz : ∀ y ∈ O, u (y,t) = 0) :
    spatialD u (x,t) = 0 ∧ spatialDD u (x,t) = 0 := by
  have he : (fun y => u (y,t)) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact hz y hy
  constructor
  · simpa [spatialD] using he.fderiv_eq (𝕜 := ℝ)
  · simpa [spatialDD] using he.fderiv.fderiv_eq (𝕜 := ℝ)

theorem timeD_zero_of_neg {n : ℕ} {O : Set (Space n)} {T : ℝ} {u : Point n → ℝ}
    (hzero : ∀ p ∈ cylinder O (-T) T, p.2 ≤ 0 → u p = 0)
    {x : Space n} {t : ℝ} (hp : (x,t) ∈ cylinder O (-T) T) (ht : t < 0) :
    timeD (cylinder O (-T) T) u (x,t) = 0 := by
  have he : (fun s => u (x,s)) =ᶠ[𝓝[{s | (x,s) ∈ cylinder O (-T) T}] t]
      (fun _ => (0 : ℝ)) := by
    have hneg : ∀ᶠ s in 𝓝 t, s < 0 := Iio_mem_nhds ht
    filter_upwards [self_mem_nhdsWithin,
      hneg.filter_mono nhdsWithin_le_nhds] with s hs hs0
    exact hzero (x,s) hs hs0.le
  simpa [timeD] using he.derivWithin_eq_of_mem hp

/-- Actual within-time derivatives vanish on the entire initial face as a
consequence of parabolic C2 continuity and vanishing at negative times. -/
theorem timeD_zero_of_nonpos {n : ℕ} {O : Set (Space n)} {T : ℝ} {u : Point n → ℝ}
    (hT : 0 < T) (hu : C2 (cylinder O (-T) T) u)
    (hzero : ∀ p ∈ cylinder O (-T) T, p.2 ≤ 0 → u p = 0)
    {x : Space n} {t : ℝ} (hp : (x,t) ∈ cylinder O (-T) T) (ht : t ≤ 0) :
    timeD (cylinder O (-T) T) u (x,t) = 0 := by
  rcases ht.lt_or_eq with ht | rfl
  · exact timeD_zero_of_neg hzero hp ht
  let s : ℕ → ℝ := fun k => -T / ((k : ℝ)+1)
  have hs (k : ℕ) : s k ∈ Set.Icc (-T) T ∧ s k < 0 := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hsk : s k < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hT) (by positivity)
    refine ⟨⟨?_, hsk.le.trans hT.le⟩,hsk⟩
    apply (le_div_iff₀ (by positivity)).2
    nlinarith
  have hs0 : Tendsto s atTop (𝓝 0) := by
    simpa [s, div_eq_mul_inv, one_div] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (-T)
  have hseq : Tendsto (fun k => (x,s k)) atTop
      (𝓝[cylinder O (-T) T] (x,0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_nhds.prodMk_nhds hs0,
      Filter.Eventually.of_forall (fun k => ⟨hp.1,(hs k).1⟩)⟩
  have hlim := (hu.2.2.2.1.continuousWithinAt hp).tendsto.comp hseq
  have he : (fun k => timeD (cylinder O (-T) T) u (x,s k)) = fun _ => (0 : ℝ) := by
    funext k
    exact timeD_zero_of_neg hzero ⟨hp.1,(hs k).1⟩ (hs k).2
  change Tendsto (fun k => timeD (cylinder O (-T) T) u (x,s k)) atTop _ at hlim
  rw [he] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- A continuous highest jet which vanishes at nonpositive times inherits its
positive-time Hölder estimate across the initial face with the same constant. -/
theorem holderBound_across_zero {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {O : Set (Space n)} {T γ C : ℝ} {f : Point n → V}
    (hT : 0 < T) (hγ : 0 < γ)
    (hcont : ContinuousOn f (cylinder O (-T) T))
    (hzero : ∀ p ∈ cylinder O (-T) T, p.2 ≤ 0 → f p = 0)
    (hpos : HolderBound γ (O ×ˢ Set.Ioc 0 T) f C) :
    HolderBound γ (cylinder O (-T) T) f C := by
  have htime (x : Space n) (hx : x ∈ O) (t : ℝ) (ht : t ∈ Set.Ioc 0 T) :
      ‖f (x,t)‖ ≤ C * t ^ (γ/2) := by
    let s : ℕ → ℝ := fun k => T / ((k : ℝ) + 1)
    have hs (k : ℕ) : s k ∈ Set.Ioc 0 T := by
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      exact ⟨div_pos hT (by positivity), (div_le_iff₀ (by positivity)).2 (by nlinarith)⟩
    have hs0 : Tendsto s atTop (𝓝 0) := by
      simpa [s, div_eq_mul_inv, one_div] using
        tendsto_one_div_add_atTop_nhds_zero_nat.const_mul T
    have hx0 : (x,0) ∈ cylinder O (-T) T := ⟨hx, by constructor <;> linarith⟩
    have hseq : Tendsto (fun k => (x,s k)) atTop
        (𝓝[cylinder O (-T) T] (x,0)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨tendsto_const_nhds.prodMk_nhds hs0, Filter.Eventually.of_forall ?_⟩
      intro k
      exact ⟨hx, (neg_nonpos.mpr hT.le).trans (hs k).1.le, (hs k).2⟩
    have hf0 := (hcont.continuousWithinAt hx0).tendsto.comp hseq
    rw [hzero (x,0) hx0 le_rfl] at hf0
    have hleft : Tendsto (fun k => ‖f (x,t) - f (x,s k)‖) atTop (𝓝 ‖f (x,t)‖) := by
      simpa using (tendsto_const_nhds.sub hf0).norm
    have hright : Tendsto (fun k => C * holderWeight γ (x,t) (x,s k))
        atTop (𝓝 (C * t ^ (γ/2))) := by
      simp only [holderWeight, sub_self, norm_zero, Real.zero_rpow hγ.ne', zero_add]
      have hdiff : Tendsto (fun k => t-s k) atTop (𝓝 t) := by
        simpa using (tendsto_const_nhds (x := t)).sub hs0
      have hlim := (hdiff.abs.rpow_const
        (Or.inr (by linarith : 0 ≤ γ/2))).const_mul C
      simpa only [sub_zero, abs_of_pos ht.1] using hlim
    exact le_of_tendsto_of_tendsto hleft hright
      (Filter.Eventually.of_forall fun k => hpos.2.2 (x,t) ⟨hx,ht⟩ (x,s k) ⟨hx,hs k⟩)
  refine ⟨hpos.1, ?_, ?_⟩
  · intro p hp
    by_cases ht : 0 < p.2
    · exact hpos.2.1 p ⟨hp.1,ht,hp.2.2⟩
    · rw [hzero p hp (le_of_not_gt ht), norm_zero]
      exact hpos.1
  · intro p hp q hq
    have hweight : 0 ≤ holderWeight γ p q := by
      exact add_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
        (Real.rpow_nonneg (abs_nonneg _) _)
    by_cases hpt : 0 < p.2
    · by_cases hqt : 0 < q.2
      · exact hpos.2.2 p ⟨hp.1,hpt,hp.2.2⟩ q ⟨hq.1,hqt,hq.2.2⟩
      · rw [hzero q hq (le_of_not_gt hqt), sub_zero]
        refine (htime p.1 hp.1 p.2 ⟨hpt,hp.2.2⟩).trans ?_
        apply mul_le_mul_of_nonneg_left _ hpos.1
        apply le_add_of_nonneg_of_le (Real.rpow_nonneg (norm_nonneg _) _)
        apply Real.rpow_le_rpow hpt.le _ (by linarith)
        rw [abs_of_nonneg (by linarith : 0 ≤ p.2-q.2)]
        linarith
    · by_cases hqt : 0 < q.2
      · rw [hzero p hp (le_of_not_gt hpt), zero_sub, norm_neg]
        refine (htime q.1 hq.1 q.2 ⟨hqt,hq.2.2⟩).trans ?_
        apply mul_le_mul_of_nonneg_left _ hpos.1
        apply le_add_of_nonneg_of_le (Real.rpow_nonneg (norm_nonneg _) _)
        apply Real.rpow_le_rpow hqt.le _ (by linarith)
        rw [abs_of_nonpos (by linarith : p.2-q.2 ≤ 0)]
        linarith
      · rw [hzero p hp (le_of_not_gt hpt), hzero q hq (le_of_not_gt hqt), sub_self,
          norm_zero]
        exact mul_nonneg hpos.1 hweight

end Yau.LeafProofs.L05Aux

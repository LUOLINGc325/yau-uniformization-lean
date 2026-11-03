import Yau.Blueprint.Alignment

/-! A genuine inverse on a lower ray, retained when the exposed clock starts later. -/

open scoped Topology
open Filter

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

theorem inverse_on_ray {r : ℝ → ℝ} {A : ℝ}
    (hr : StrictMonoOn r (Set.Ici A)) (hc : ContinuousOn r (Set.Ici A))
    (hinf : Tendsto r atTop atTop) :
    ∃ time : ℝ → ℝ,
      (∀ s, r A ≤ s → A ≤ time s ∧ r (time s) = s) ∧
      (∀ t, A ≤ t → time (r t) = t) ∧
      StrictMonoOn time (Set.Ici (r A)) ∧ Tendsto time atTop atTop := by
  have hsur : ∀ s, r A ≤ s → ∃ t, A ≤ t ∧ r t = s := by
    intro s hs
    obtain ⟨T, hT⟩ := (tendsto_atTop_atTop.1 hinf) s
    have hcont : ContinuousOn r (Set.Icc A (max A T)) :=
      hc.mono fun _ ht => ht.1
    obtain ⟨t, ht, hrt⟩ := intermediate_value_Icc (le_max_left A T) hcont
      ⟨hs, hT _ (le_max_right A T)⟩
    exact ⟨t, ht.1, hrt⟩
  let time : ℝ → ℝ := fun s => if hs : r A ≤ s then (hsur s hs).choose else A
  have htime : ∀ s, r A ≤ s → A ≤ time s ∧ r (time s) = s := by
    intro s hs
    simpa only [time, dite_eq_left hs] using (hsur s hs).choose_spec
  have hleft : ∀ t, A ≤ t → time (r t) = t := by
    intro t ht
    have hrt : r A ≤ r t := hr.monotoneOn (le_refl A) ht ht
    exact hr.injOn (htime _ hrt).1 ht (htime _ hrt).2
  refine ⟨time, htime, hleft, ?_, ?_⟩
  · intro s hs s' hs' hss'
    by_contra hn
    have hle : time s' ≤ time s := le_of_not_gt hn
    have := hr.monotoneOn (htime _ hs').1 (htime _ hs).1 hle
    rw [(htime _ hs').2, (htime _ hs).2] at this
    exact (not_le_of_gt hss') this
  · apply tendsto_atTop_atTop.2
    intro B
    refine ⟨max (r A) (r (max A B)), ?_⟩
    intro s hs
    have hsA : r A ≤ s := (le_max_left _ _).trans hs
    have hsB : r (max A B) ≤ s := (le_max_right _ _).trans hs
    have hinv := htime s hsA
    have hAB : max A B ≤ time s := by
      by_contra hn
      have hh := hr hinv.1 (le_max_left A B) (lt_of_not_ge hn)
      rw [hinv.2] at hh
      exact (not_lt_of_ge hsB) hh
    exact (le_max_right A B).trans hAB

theorem inverseClock_of_ricciWindows {n : ℕ} {X : KahlerManifold n}
    (o : Pt X) (h : Flow X) (ρ : STF X) (t₀ : ℝ)
    (hWindows : RicciWindows X o h ρ) :
    ∃ (time : ℝ → ℝ) (s₀ a₀ b₀ : ℝ),
      ClockParameter X o h ρ time s₀ ∧ 0 < a₀ ∧ a₀ < 1 ∧ 0 < b₀ ∧
      ClockRateInput o h time s₀ a₀ b₀ ∧
      (∀ s, s₀ ≤ s → t₀ ≤ time s) ∧
      (∀ s, s₀ ≤ s → 0 < time (a₀ * s) ∧ ρ o (time (a₀ * s)) = a₀ * s) := by
  rcases hWindows with
    ⟨⟨t₁, ht₁, hr, hq, hd⟩, ⟨c, hc, t₂, hcb⟩, hlim, _, hlow, _, _,
      ⟨a₀, b₀, ha₀, ha₁, hb₀, ⟨Tᵣ, hric⟩, _⟩⟩
  obtain ⟨Tpos, hTpos⟩ := (tendsto_atTop_atTop.1 hlim) 1
  let A := max Tpos (max t₁ (max t₂ (max Tᵣ (max t₀ 1))))
  have hAposBound : Tpos ≤ A := le_max_left _ _
  have hA₁ : t₁ ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hA₂ : t₂ ≤ A :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hAᵣ : Tᵣ ≤ A :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have hA₀ : t₀ ≤ A :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))))
  have hAone : 1 ≤ A :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))))
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hAone
  have hrA : 0 < ρ o A := lt_of_lt_of_le zero_lt_one (hTpos A hAposBound)
  have hmono : StrictMonoOn (ρ o) (Set.Ici A) := hr.mono fun _ ht => hA₁.trans ht
  have hcont : ContinuousOn (ρ o) (Set.Ici A) := by
    intro t ht
    exact (hd t (hA₁.trans ht)).continuousAt.continuousWithinAt
  obtain ⟨time, htime, hleft, hstrict, htlim⟩ := inverse_on_ray hmono hcont hlim
  let s₀ := ρ o A / a₀
  have hs₀ : 0 < s₀ := div_pos hrA ha₀
  have hrAs₀ : ρ o A ≤ s₀ := by
    dsimp [s₀]
    exact (le_div_iff₀ ha₀).2 (by nlinarith)
  have has : ∀ s, s₀ ≤ s → ρ o A ≤ a₀ * s := by
    intro s hs
    have hprod := mul_le_mul_of_nonneg_left hs ha₀.le
    dsimp [s₀] at hprod
    have heq : a₀ * (ρ o A / a₀) = ρ o A := by field_simp
    rwa [heq] at hprod
  have hinv : ∀ s, s₀ ≤ s → A ≤ time s ∧ ρ o (time s) = s :=
    fun s hs => htime s (hrAs₀.trans hs)
  refine ⟨time, s₀, a₀, b₀, ?_, ha₀, ha₁, hb₀, ?_, ?_, ?_⟩
  · refine ⟨hs₀, hstrict.mono (fun _ hs => hrAs₀.trans hs), ?_, htlim⟩
    intro s hs
    exact ⟨hApos.trans_le (hinv s hs).1, (hinv s hs).2⟩
  · refine ⟨?_, ⟨c, hc, ?_⟩, ?_, ?_⟩
    · intro s hs s' hs' hss'
      exact hq (hA₁.trans (hinv s hs).1) (hA₁.trans (hinv s' hs').1)
        ((hstrict.mono fun _ hx => hrAs₀.trans hx).monotoneOn hs hs' hss')
    · intro s hs
      exact hcb _ (hA₂.trans (hinv s hs).1)
    · intro eps heps S
      let target := max S s₀
      have htarg : s₀ ≤ target := le_max_right _ _
      obtain ⟨t, ht, hbound⟩ := hlow eps heps (time target)
      have hAt : A ≤ t := (hinv target htarg).1.trans ht
      have hst : target ≤ ρ o t := by
        rw [← (hinv target htarg).2]
        exact hmono.monotoneOn (hinv target htarg).1 hAt ht
      refine ⟨ρ o t, hst, ?_⟩
      simpa only [hleft t hAt] using hbound
    · intro s hs
      have hsmall := htime (a₀ * s) (has s hs)
      apply hric (time s) (time (a₀ * s)) (hAᵣ.trans (hinv s hs).1)
        (hApos.le.trans hsmall.1)
      change ρ o (time (a₀ * s)) = a₀ * ρ o (time s)
      rw [hsmall.2, (hinv s hs).2]
  · intro s hs
    exact hA₀.trans (hinv s hs).1
  · intro s hs
    have hsmall := htime (a₀ * s) (has s hs)
    exact ⟨hApos.trans_le hsmall.1, hsmall.2⟩

end Yau.Blueprint.Alignment.Y03Proof

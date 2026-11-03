import spec.CHAIN.CONTRACTS

/-! A positive multiple of an actual exhaustion forces a bounded-above
continuous function to attain its space-time maximum. -/
noncomputable section
open Set
namespace Yau.NodeProofs.F01Aux
variable {A : Type*} [TopologicalSpace A]

theorem exists_spaceTime_max_of_proper_penalty
    (f : A → ℝ) (hproper : ∀ c : ℝ, IsCompact {x | f x ≤ c})
    (J : Set ℝ) (hJ : IsCompact J) (F : A × ℝ → ℝ)
    (hF : ContinuousOn F (univ ×ˢ J))
    {δ B : ℝ} (hδ : 0 < δ)
    (hupper : ∀ p : A × ℝ, p.2 ∈ J → F p ≤ B - δ * f p.1)
    (a₀ : A) (t₀ : ℝ) (ht₀ : t₀ ∈ J) :
    ∃ p : A × ℝ, p.2 ∈ J ∧ IsMaxOn F (univ ×ˢ J) p := by
  let R := (B - F (a₀, t₀)) / δ
  have hR : δ * R = B - F (a₀, t₀) := by
    dsimp [R]
    exact mul_div_cancel₀ _ hδ.ne'
  have hbase : f a₀ ≤ R := by
    have h := hupper (a₀, t₀) ht₀
    nlinarith
  have hcomp := (hproper R).prod hJ
  have hsub : {x | f x ≤ R} ×ˢ J ⊆ (univ : Set A) ×ˢ J :=
    fun _ hp => ⟨mem_univ _, hp.2⟩
  obtain ⟨p, hp, hmax⟩ := hcomp.exists_isMaxOn
    (show ({x | f x ≤ R} ×ˢ J).Nonempty from ⟨(a₀, t₀), hbase, ht₀⟩) (hF.mono hsub)
  refine ⟨p, hp.2, ?_⟩
  intro q hq
  change F q ≤ F p
  by_cases hqR : f q.1 ≤ R
  · exact hmax ⟨hqR, hq.2⟩
  · have hbaseMax := hmax (show (a₀, t₀) ∈ {x | f x ≤ R} ×ˢ J from ⟨hbase, ht₀⟩)
    change F (a₀, t₀) ≤ F p at hbaseMax
    have hu := hupper q hq.2
    have hh := mul_lt_mul_of_pos_left (lt_of_not_ge hqR) hδ
    nlinarith

end Yau.NodeProofs.F01Aux

import Yau.Proofs.Y03WeightCut
import Yau.Proofs.Y03GraphMatrix

/-! The finite weight cuts retain every real threshold and repeated-weight block exactly. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

variable {n : ℕ}

def weightValueSet (w : Fin n → ℝ) : Finset ℝ := Finset.univ.image w

def weightValueEmbedding (w : Fin n → ℝ) : Fin (weightValueSet w).card ↪o ℝ :=
  (weightValueSet w).orderEmbOfFin rfl

def weightRankIndex (w : Fin n → ℝ) (i : Fin n) : Fin (weightValueSet w).card :=
  ((weightValueSet w).orderIsoOfFin rfl).symm
    ⟨w i, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩

theorem weightValueEmbedding_rank (w : Fin n → ℝ) (i : Fin n) :
    weightValueEmbedding w (weightRankIndex w i) = w i := by
  change (((weightValueSet w).orderIsoOfFin rfl)
    (((weightValueSet w).orderIsoOfFin rfl).symm
      ⟨w i, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩) : ℝ) = w i
  rw [OrderIso.apply_symm_apply]

def oldWeightLevel (w : Fin n → ℝ) (r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (weightRankIndex w i).val < r)

def newWeightLevel (wold wnew : Fin n → ℝ) (r : ℕ) : Finset (Fin n) :=
  if hr : r < (weightValueSet wold).card then
    Finset.univ.filter (fun i => wnew i < weightValueEmbedding wold ⟨r, hr⟩)
  else Finset.univ

theorem oldWeightLevel_mono (w : Fin n → ℝ) : Monotone (oldWeightLevel w) := by
  intro r s hrs i hi
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ((Finset.mem_filter.1 hi).2).trans_le hrs⟩

theorem newWeightLevel_mono (wold wnew : Fin n → ℝ) : Monotone (newWeightLevel wold wnew) := by
  intro r s hrs i hi
  by_cases hs : s < (weightValueSet wold).card
  · have hr : r < (weightValueSet wold).card := hrs.trans_lt hs
    rw [newWeightLevel, dite_eq_left hr] at hi
    rw [newWeightLevel, dite_eq_left hs]
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ((Finset.mem_filter.1 hi).2).trans_le
      ((weightValueEmbedding wold).monotone hrs)⟩
  · rw [newWeightLevel, dite_eq_right hs]
    exact Finset.mem_univ _

theorem oldWeightLevel_top (w : Fin n → ℝ) {r : ℕ} (hr : (weightValueSet w).card ≤ r) :
    oldWeightLevel w r = Finset.univ := by
  ext i
  simp only [oldWeightLevel, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact (weightRankIndex w i).isLt.trans_le hr

theorem weightLevel_separated (wold wnew : Fin n → ℝ) (r : ℕ) :
    ∀ i ∈ newWeightLevel wold wnew r, ∀ l, l ∉ oldWeightLevel wold r → wnew i < wold l := by
  intro i hi l hl
  by_cases hr : r < (weightValueSet wold).card
  · rw [newWeightLevel, dite_eq_left hr] at hi
    have hlrank : r ≤ (weightRankIndex wold l).val := by
      by_contra hn
      exact hl (Finset.mem_filter.2 ⟨Finset.mem_univ _, lt_of_not_ge hn⟩)
    have he := (weightValueEmbedding wold).monotone (a := ⟨r, hr⟩) (b := weightRankIndex wold l) hlrank
    rw [weightValueEmbedding_rank] at he
    exact ((Finset.mem_filter.1 hi).2).trans_le he
  · rw [oldWeightLevel_top wold (le_of_not_gt hr)] at hl
    exact (hl (Finset.mem_univ _)).elim

theorem oldWeightLevel_cut (w : Fin n → ℝ) (x : ℝ) :
    oldWeightLevel w (orderedCutIndex (weightValueEmbedding w) x) = lowerWeightSet w x := by
  ext i
  simp only [oldWeightLevel, lowerWeightSet, Finset.mem_filter, Finset.mem_univ, true_and]
  simpa only [weightValueEmbedding_rank] using orderedCutIndex_spec (weightValueEmbedding w) x (weightRankIndex w i)

theorem newWeightLevel_cut_covers (wold wnew : Fin n → ℝ) (x : ℝ) :
    lowerWeightSet wnew x ⊆ newWeightLevel wold wnew (orderedCutIndex (weightValueEmbedding wold) x) := by
  intro i hi
  let r := orderedCutIndex (weightValueEmbedding wold) x
  by_cases hr : r < (weightValueSet wold).card
  · have hex : x < weightValueEmbedding wold ⟨r, hr⟩ := by
      by_contra hn
      have h := (orderedCutIndex_spec (weightValueEmbedding wold) x ⟨r, hr⟩).2 (le_of_not_gt hn)
      exact (Nat.lt_irrefl r) h
    rw [newWeightLevel, dite_eq_left hr]
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ((Finset.mem_filter.1 hi).2).trans_lt hex⟩
  · rw [newWeightLevel, dite_eq_right hr]
    exact Finset.mem_univ _

theorem weightValueSet_card_le (w : Fin n → ℝ) : (weightValueSet w).card ≤ n := by
  exact (Finset.card_image_le).trans_eq (by simp)

end Yau.Blueprint.Alignment.Y03Proof

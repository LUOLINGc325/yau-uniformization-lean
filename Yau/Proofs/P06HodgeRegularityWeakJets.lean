import Yau.Proofs.P06HodgeRegularityWeakProducts

/-! Finite actual weak jets in fixed coordinate directions, before any
choice of Euclidean coordinate equivalence or representative smoothing. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux

variable {E ι α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]

def regularityWeakJet (ν : Measure E) (O : Set E) (v : ι → E) (s : ℕ)
    (U : E → α → ℝ) (J : List ι → E → α → ℝ) : Prop :=
  J [] = U ∧
    (∀ w, w.length ≤ s → ∀ c, MemLp (fun z => J w z c) 2 (ν.restrict O)) ∧
    ∀ w, w.length < s → ∀ i c,
      regularityWeakDeriv ν O (v i) (fun z => J w z c) (fun z => J (i::w) z c)

theorem regularityWeakJet_mono_region (ν : Measure E) [IsLocallyFiniteMeasure ν]
    {O V : Set E} {v : ι → E} {s : ℕ}
    {U : E → α → ℝ} {J : List ι → E → α → ℝ}
    (h : regularityWeakJet ν O v s U J) (hVO : V ⊆ O) : regularityWeakJet ν V v s U J :=
  ⟨h.1, fun w hw c => (h.2.1 w hw c).mono_measure (Measure.restrict_mono hVO le_rfl),
    fun w hw i c => regularityWeakDeriv_mono ν (h.2.2 w hw i c) hVO⟩

theorem regularityWeakJet_mono_order (ν : Measure E) {O : Set E} {v : ι → E} {s t : ℕ}
    {U : E → α → ℝ} {J : List ι → E → α → ℝ}
    (h : regularityWeakJet ν O v s U J) (hts : t ≤ s) : regularityWeakJet ν O v t U J :=
  ⟨h.1, fun w hw => h.2.1 w (hw.trans hts), fun w hw => h.2.2 w (hw.trans_le hts)⟩

def regularityTwoJet (U : E → α → ℝ) (G : E → ι → α → ℝ) (H : E → ι → ι → α → ℝ) :
    List ι → E → α → ℝ
  | [] => U
  | [i] => fun z c => G z i c
  | [i,j] => fun z c => H z i j c
  | _ => 0

theorem regularityTwoJet_isWeakJet (ν : Measure E) (O : Set E) (v : ι → E)
    (U : E → α → ℝ) (G : E → ι → α → ℝ) (H : E → ι → ι → α → ℝ)
    (hU : ∀ c, MemLp (fun z => U z c) 2 (ν.restrict O))
    (hG : ∀ i c, MemLp (fun z => G z i c) 2 (ν.restrict O))
    (hH : ∀ i j c, MemLp (fun z => H z i j c) 2 (ν.restrict O))
    (hWG : ∀ i c, regularityWeakDeriv ν O (v i) (fun z => U z c) (fun z => G z i c))
    (hWH : ∀ i j c, regularityWeakDeriv ν O (v i) (fun z => G z j c) (fun z => H z i j c)) :
    regularityWeakJet ν O v 2 U (regularityTwoJet U G H) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro w hw c
    cases w with
    | nil => exact hU c
    | cons i w =>
      cases w with
      | nil => exact hG i c
      | cons j w =>
        cases w with
        | nil => exact hH i j c
        | cons k w => simp only [List.length_cons] at hw; omega
  · intro w hw i c
    cases w with
    | nil => exact hWG i c
    | cons j w =>
      cases w with
      | nil => exact hWH i j c
      | cons k w => simp only [List.length_cons] at hw; omega

theorem regularityWeakJet_standard_coordinates {d : ℕ} [Fintype α]
    (s : ℕ) (O : Set (HodgeCoordSpace d)) (U : HodgeCoordSpace d → α → ℝ)
    (J : List (Fin d) → HodgeCoordSpace d → α → ℝ) :
    regularityWeakJet volume O (fun i => Pi.single i 1) s U J ↔ HodgeCoordinateWeakJet s O U J := Iff.rfl

end Yau.NodeProofs.P06Aux

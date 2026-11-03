import Yau.LeafProofs.L16WeakWordStep

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

def initialWeakWordFamily {n : ℕ} (u : Point n → ℝ) (G : Point n → Yau.RIdx n → ℝ) :
    List (Yau.RIdx n) → Point n → ℝ
  | [] => u
  | [j] => fun p => G p j
  | _ => 0

theorem initialWeakWordFamily_state {n : ℕ} {Q : Set (Point n)}
    {a : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ}
    {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hu : MemLp u 2 (volume.restrict Q))
    (hG : ∀ j, MemLp (fun p => G p j) 2 (volume.restrict Q))
    (hWG : WeakGradientOn Q u G)
    (hEq : WeakDivergenceEvolutionOn Q u (energyFlux a G) (fun p => ∑ j, c p j*G p j)) :
    WeakSpatialWordState Q a c 0 (initialWeakWordFamily u G) := by
  refine ⟨?_,?_,?_⟩
  · intro w hw
    cases w with
    | nil => exact hu
    | cons j w =>
      cases w with
      | nil => exact hG j
      | cons i w => simp only [List.length_cons,List.length_nil] at hw; omega
  · intro w hw
    have hw0 : w = [] := List.length_eq_zero_iff.mp (by omega)
    subst w
    exact hWG
  · intro w hw
    have hw0 : w = [] := List.length_eq_zero_iff.mp (by omega)
    subst w
    have hP : weakWordFlux a (initialWeakWordFamily u G) [] = energyFlux a G := by
      funext p q
      simp only [weakWordFlux,weakWordSource_nil,Pi.zero_apply,add_zero]
      rfl
    have hR : weakWordDrift c (initialWeakWordFamily u G) [] = (fun p => ∑ j, c p j*G p j) := by
      funext p
      simp only [weakWordDrift,weakWordSource_nil,Pi.zero_apply,add_zero]
      rfl
    rw [hP,hR]
    exact hEq

theorem exists_finite_weakSpatialWordState {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    {a : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {lam upper C : ℝ}
    (hC : 0 ≤ C) (hEll : Elliptic Q a lam upper)
    (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    (hc : ∀ j, ContDiff ℝ ∞ (fun p => c p j))
    (hcc : ∀ j, HasCompactSupport (fun p => c p j))
    (hAVal : ∀ p, ‖a p‖ ≤ C) (hCVal : ∀ j p, |c p j| ≤ C)
    (hADq : ∀ i h p, ‖spatialDifferenceQuotient a (Yau.realVec i) h p‖ ≤ C)
    (hCDq : ∀ j i h p, |spatialDifferenceQuotient (fun q => c q j) (Yau.realVec i) h p| ≤ C)
    (U0 : List (Yau.RIdx n) → Point n → ℝ)
    (hBase : WeakSpatialWordState Q a c 0 U0) :
    ∀ k : ℕ, ∀ V : Set (Point n), IsOpen V → IsCompact (closure V) → closure V ⊆ Q →
      ∃ U : List (Yau.RIdx n) → Point n → ℝ,
        (∀ v, v.length ≤ 1 → U v = U0 v) ∧ WeakSpatialWordState V a c k U := by
  intro k
  induction k with
  | zero =>
    intro V hV hVC hVQ
    exact ⟨U0,fun _ _ => rfl,weakSpatialWordState_mono hBase (subset_closure.trans hVQ)⟩
  | succ k ih =>
    intro V hV hVC hVQ
    obtain ⟨W,hW,hVW,hWQ,hWC⟩ := exists_open_between_and_isCompact_closure hVC hQ hVQ
    obtain ⟨U,hU0,hState⟩ := ih W hW hWC hWQ
    have hEllW : Elliptic W a lam upper :=
      ⟨hEll.1,hEll.2.1,fun p hp => hEll.2.2 p (hWQ (subset_closure hp))⟩
    obtain ⟨U',hOld,hState'⟩ := weakSpatialWordState_step hW hV hVC hVW hC hEllW ha hca hc hcc
      hAVal hCVal hADq hCDq k U hState
    exact ⟨U',fun v hv => (hOld v (by omega)).trans (hU0 v hv),hState'⟩

theorem finite_weak_spatial_words_of_divergence_evolution {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    {a : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {lam upper C : ℝ}
    (hC : 0 ≤ C) (hEll : Elliptic Q a lam upper)
    (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    (hc : ∀ j, ContDiff ℝ ∞ (fun p => c p j))
    (hcc : ∀ j, HasCompactSupport (fun p => c p j))
    (hAVal : ∀ p, ‖a p‖ ≤ C) (hCVal : ∀ j p, |c p j| ≤ C)
    (hADq : ∀ i h p, ‖spatialDifferenceQuotient a (Yau.realVec i) h p‖ ≤ C)
    (hCDq : ∀ j i h p, |spatialDifferenceQuotient (fun q => c q j) (Yau.realVec i) h p| ≤ C)
    {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hu : MemLp u 2 (volume.restrict Q))
    (hG : ∀ j, MemLp (fun p => G p j) 2 (volume.restrict Q))
    (hWG : WeakGradientOn Q u G)
    (hEq : WeakDivergenceEvolutionOn Q u (energyFlux a G) (fun p => ∑ j, c p j*G p j))
    (k : ℕ) {V : Set (Point n)} (hV : IsOpen V) (hVC : IsCompact (closure V)) (hVQ : closure V ⊆ Q) :
    ∃ U : List (Yau.RIdx n) → Point n → ℝ,
      U [] = u ∧ (∀ j, U [j] = fun p => G p j) ∧ WeakSpatialWordState V a c k U := by
  obtain ⟨U,hU0,hState⟩ := exists_finite_weakSpatialWordState hQ hC hEll ha hca hc hcc
    hAVal hCVal hADq hCDq (initialWeakWordFamily u G) (initialWeakWordFamily_state hu hG hWG hEq)
    k V hV hVC hVQ
  exact ⟨U,hU0 [] (by simp),fun j => hU0 [j] (by simp),hState⟩

end Yau.LeafProofs.L16Aux

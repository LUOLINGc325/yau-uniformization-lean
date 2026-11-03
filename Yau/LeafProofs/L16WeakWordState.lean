import Yau.LeafProofs.L16WeakWordEquation
import Yau.LeafProofs.L16LocalInhomogeneousGain

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- A finite collection of concrete weak derivatives and distributional equations. -/
def WeakSpatialWordState {n : ℕ} (Q : Set (Point n)) (a : Point n → Mat n)
    (c : Point n → Yau.RIdx n → ℝ) (k : ℕ)
    (U : List (Yau.RIdx n) → Point n → ℝ) : Prop :=
  (∀ w, w.length ≤ k+1 → MemLp (U w) 2 (volume.restrict Q)) ∧
  (∀ w, w.length ≤ k → WeakGradientOn Q (U w) (fun p i => U (i::w) p)) ∧
  (∀ w, w.length ≤ k → WeakDivergenceEvolutionOn Q (U w) (weakWordFlux a U w) (weakWordDrift c U w))

theorem weakWordSource_congr_of_low_eq {n : ℕ} (m : ℕ)
    (g : Yau.RIdx n → Point n → ℝ)
    {U V : List (Yau.RIdx n) → Point n → ℝ}
    (hUV : ∀ v, v.length ≤ m → U v = V v)
    (w : List (Yau.RIdx n)) (hw : w.length ≤ m) :
    weakWordSource g U w = weakWordSource g V w := by
  funext p
  unfold weakWordSource
  apply congrArg List.sum
  apply List.map_congr_left
  intro st hst
  unfold weakWordCorrection
  apply Finset.sum_congr rfl
  intro j _
  have hLen := commutatorSplits_lower_length w st hst
  rw [hUV (j::st.2) (by simp only [List.length_cons]; omega)]

theorem weakWordFlux_congr_of_low_eq {n : ℕ} (m : ℕ) (a : Point n → Mat n)
    {U V : List (Yau.RIdx n) → Point n → ℝ}
    (hUV : ∀ v, v.length ≤ m+1 → U v = V v)
    (w : List (Yau.RIdx n)) (hw : w.length ≤ m) :
    weakWordFlux a U w = weakWordFlux a V w := by
  funext p q
  have hSource := weakWordSource_congr_of_low_eq (m+1) (fun j p => a p q j) hUV w (by omega)
  unfold weakWordFlux energyFlux
  rw [hSource]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun f : Point n → ℝ => a p q j*f p)
    (hUV (j::w) (by simp only [List.length_cons]; omega))

theorem weakWordDrift_congr_of_low_eq {n : ℕ} (m : ℕ) (c : Point n → Yau.RIdx n → ℝ)
    {U V : List (Yau.RIdx n) → Point n → ℝ}
    (hUV : ∀ v, v.length ≤ m+1 → U v = V v)
    (w : List (Yau.RIdx n)) (hw : w.length ≤ m) :
    weakWordDrift c U w = weakWordDrift c V w := by
  funext p
  have hSource := weakWordSource_congr_of_low_eq (m+1) (fun j p => c p j) hUV w (by omega)
  unfold weakWordDrift
  rw [hSource]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [hUV (j::w) (by simp only [List.length_cons]; omega)]

theorem weakSpatialWordState_mono {n : ℕ} {Q V : Set (Point n)}
    {a : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {k : ℕ}
    {U : List (Yau.RIdx n) → Point n → ℝ}
    (hState : WeakSpatialWordState Q a c k U) (hVQ : V ⊆ Q) :
    WeakSpatialWordState V a c k U := by
  exact ⟨fun w hw => (hState.1 w hw).mono_measure (Measure.restrict_mono hVQ le_rfl),
    fun w hw => weakGradientOn_mono (hState.2.1 w hw) hVQ,
    fun w hw => weakDivergenceEvolutionOn_mono (hState.2.2 w hw) hVQ⟩

theorem weakSpatialWordState_congr_of_low_eq {n : ℕ} {Q : Set (Point n)}
    {a : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {k : ℕ}
    {U V : List (Yau.RIdx n) → Point n → ℝ}
    (hState : WeakSpatialWordState Q a c k U)
    (hVU : ∀ v, v.length ≤ k+1 → V v = U v) :
    WeakSpatialWordState Q a c k V := by
  refine ⟨fun w hw => ?_,fun w hw => ?_,fun w hw => ?_⟩
  · rw [hVU w hw]
    exact hState.1 w hw
  · have hGrad : (fun p i => V (i::w) p) = fun p i => U (i::w) p := by
      funext p i
      rw [hVU (i::w) (by simp only [List.length_cons]; omega)]
    rw [hVU w (by omega),hGrad]
    exact hState.2.1 w hw
  · rw [hVU w (by omega),weakWordFlux_congr_of_low_eq k a hVU w hw,
      weakWordDrift_congr_of_low_eq k c hVU w hw]
    exact hState.2.2 w hw

def extendWeakWordFamily {n : ℕ} (k : ℕ)
    (U : List (Yau.RIdx n) → Point n → ℝ)
    (Z : {w : List (Yau.RIdx n) // w.length = k} → Yau.RIdx n → Yau.RIdx n → Point n → ℝ) :
    List (Yau.RIdx n) → Point n → ℝ
  | i::j::w => if h : w.length = k then Z ⟨w,h⟩ i j else U (i::j::w)
  | w => U w

theorem extendWeakWordFamily_eq_old {n : ℕ} (k : ℕ)
    (U : List (Yau.RIdx n) → Point n → ℝ)
    (Z : {w : List (Yau.RIdx n) // w.length = k} → Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (v : List (Yau.RIdx n)) (hv : v.length ≤ k+1) :
    extendWeakWordFamily k U Z v = U v := by
  cases v with
  | nil => rfl
  | cons i v =>
    cases v with
    | nil => rfl
    | cons j w =>
      have hNe : w.length ≠ k := by simp only [List.length_cons] at hv; omega
      simp only [extendWeakWordFamily,dif_neg hNe]

theorem extendWeakWordFamily_eq_new {n : ℕ} (k : ℕ)
    (U : List (Yau.RIdx n) → Point n → ℝ)
    (Z : {w : List (Yau.RIdx n) // w.length = k} → Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (w : {w : List (Yau.RIdx n) // w.length = k}) (i j : Yau.RIdx n) :
    extendWeakWordFamily k U Z (i::j::w.1) = Z w i j := by
  simp only [extendWeakWordFamily,dif_pos w.2]

end Yau.LeafProofs.L16Aux

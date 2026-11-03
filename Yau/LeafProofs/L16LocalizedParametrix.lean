import Yau.LeafProofs.L16ParametrixBounds

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section

namespace Yau.LeafProofs.L16Aux

open Yau.Parabolic Yau.ParabolicCandidates

def localizationIndices {n : ℕ} (s : Finset (Space n)) : Finset (Option (Space n)) :=
  insert none (s.image some)

theorem localizationIndices_sum {n : ℕ} (s : Finset (Space n))
    (f : Option (Space n) → ℝ) :
    (∑ i ∈ localizationIndices s, f i) = (∑ c ∈ s, f (some c))+f none := by
  classical
  rw [localizationIndices,Finset.sum_insert (by simp),Finset.sum_image]
  · ring
  · intro c _ d _ h
    exact Option.some.inj h

def localizationEquiv {n : ℕ} (B : Space n → Space n ≃L[ℝ] Space n)
    (Bext : Space n ≃L[ℝ] Space n) : Option (Space n) → Space n ≃L[ℝ] Space n
  | none => Bext
  | some c => B c

def localizationOuter {n : ℕ} (s : Finset (Space n)) {r : ℝ} (hr : 0 < r) :
    Option (Space n) → Space n → ℝ
  | none => exteriorCutoff s r hr
  | some c => outerPatchBump r hr c

def localizationSource {n : ℕ} (s : Finset (Space n)) {r : ℝ} (hr : 0 < r) :
    Option (Space n) → Space n → ℝ
  | none => exteriorSourceCutoff s r hr
  | some c => normalizedPatchCutoff s r hr c

def localizationFrozenMatrix {n : ℕ} (a : Point n → Mat n) : Option (Space n) → Mat n
  | none => 1
  | some c => a (c,0)

def localizedHeatParametrix {n : ℕ} (s : Finset (Space n)) {r : ℝ} (hr : 0 < r)
    (B : Space n → Space n ≃L[ℝ] Space n) (Bext : Space n ≃L[ℝ] Space n)
    (f : Point n → ℝ) : Point n → ℝ :=
  finiteHeatParametrix (localizationIndices s) (localizationEquiv B Bext)
    (localizationOuter s hr) (localizationSource s hr) f

theorem localizationOuter_contDiff {n : ℕ} (s : Finset (Space n)) {r : ℝ} (hr : 0 < r)
    (i : Option (Space n)) : ContDiff ℝ 2 (localizationOuter s hr i) := by
  cases i with
  | none => exact (exteriorCutoff_contDiff s hr).of_le (by norm_num)
  | some c => exact (outerPatchBump r hr c).contDiff

theorem localizationSource_holderBound {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ P : ℝ, 0 < P ∧ ∀ (s : Finset (Space n)) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      (∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖) → ∀ T : ℝ,
      ∀ i : Option (Space n), HolderBound α (cylinder Set.univ 0 T)
        (fun p => localizationSource s hr i p.1) (P*r⁻¹*r^(1-α)) := by
  obtain ⟨P,hP,hSource⟩ := source_cutoffs_uniform_holderBound (n := n) hα hα1
  refine ⟨P,hP,?_⟩
  intro s r hr hr1 hSep T i
  cases i with
  | none => exact (hSource s r hr hr1 hSep T).2
  | some c => exact (hSource s r hr hr1 hSep T).1 c

theorem localizedHeatParametrix_initial {n : ℕ} (s : Finset (Space n)) {r : ℝ} (hr : 0 < r)
    (B : Space n → Space n ≃L[ℝ] Space n) (Bext : Space n ≃L[ℝ] Space n)
    (f : Point n → ℝ) (x : Space n) : localizedHeatParametrix s hr B Bext f (x,0) = 0 :=
  finiteHeatParametrix_initial _ _ _ _ _ _

theorem localizedHeatParametrix_C2 {n : ℕ} {α T F : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (s : Finset (Space n)) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hSep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖)
    (B : Space n → Space n ≃L[ℝ] Space n) (Bext : Space n ≃L[ℝ] Space n)
    {f : Point n → ℝ} (hf : HolderBound α (cylinder Set.univ 0 T) f F) :
    C2 (cylinder Set.univ 0 T) (localizedHeatParametrix s hr B Bext f) := by
  obtain ⟨P,hP,hSource⟩ := localizationSource_holderBound (n := n) hα hα1
  exact finiteHeatParametrix_C2 _ _ _ _ hα hα1 hT hT1
    (fun i _ => localizationOuter_contDiff s hr i)
    (fun i _ => hSource s r hr hr1 hSep T i) hf

theorem localizedHeatParametrix_linearOp {n : ℕ} {α T F : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (s : Finset (Space n)) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hSep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖)
    (B : Space n → Space n ≃L[ℝ] Space n) (Bext : Space n ≃L[ℝ] Space n)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    (hB : ∀ i ∈ localizationIndices s, ∀ H : Space n →L[ℝ] Space n →L[ℝ] ℝ,
      (∑ k : Yau.RIdx n, H (localizationEquiv B Bext i (Yau.realVec k))
        (localizationEquiv B Bext i (Yau.realVec k))) =
        ∑ j : Yau.RIdx n, ∑ k : Yau.RIdx n,
          localizationFrozenMatrix a i j k*H (Yau.realVec j) (Yau.realVec k))
    {f : Point n → ℝ} (hf : HolderBound α (cylinder Set.univ 0 T) f F)
    {p : Point n} (hp : p ∈ cylinder Set.univ 0 T) :
    linearOp (cylinder Set.univ 0 T) a b (localizedHeatParametrix s hr B Bext f) p =
      f p+localizedHeatResidual T s r hr B Bext a b f p := by
  obtain ⟨P,hP,hSource⟩ := localizationSource_holderBound (n := n) hα hα1
  have hPartition (q : Point n) (hq : q ∈ cylinder Set.univ 0 T) :
      (∑ i ∈ localizationIndices s, localizationOuter s hr i q.1*localizationSource s hr i q.1) = 1 := by
    rw [localizationIndices_sum]
    exact patchCutoffs_partition s hr q.1
  have hOp := finiteHeatParametrix_linearOp (localizationIndices s) (localizationEquiv B Bext)
    (localizationOuter s hr) (localizationSource s hr) (localizationFrozenMatrix a) a b
    hα hα1 hT hT1 (fun i _ => localizationOuter_contDiff s hr i)
    (fun i _ => hSource s r hr hr1 hSep T i) hf hB hPartition hp
  change linearOp (cylinder Set.univ 0 T) a b (localizedHeatParametrix s hr B Bext f) p = _ at hOp
  rw [localizationIndices_sum] at hOp
  exact hOp

end Yau.LeafProofs.L16Aux

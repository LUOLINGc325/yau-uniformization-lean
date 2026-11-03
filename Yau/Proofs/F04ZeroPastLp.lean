import Yau.Proofs.F04ZeroPastCutoff
import Yau.LeafProofs.L16LocalEnergy

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic Yau.LeafProofs.L16Aux

def zeroPast {n : ℕ} (u : Point n → ℝ) : Point n → ℝ :=
  {p | 0 < p.2}.indicator u

theorem zeroPast_of_pos {n : ℕ} (u : Point n → ℝ) {p : Point n}
    (hp : 0 < p.2) : zeroPast u p = u p := by
  exact indicator_of_mem (show p ∈ {q : Point n | 0 < q.2} from hp) u

theorem zeroPast_of_nonpos {n : ℕ} (u : Point n → ℝ) {p : Point n}
    (hp : p.2 ≤ 0) : zeroPast u p = 0 := by
  exact indicator_of_notMem (show p ∉ {q : Point n | 0 < q.2} from not_lt.mpr hp) u

theorem zeroPast_positive_inter {n : ℕ} (O : Set (Space n)) {l s : ℝ} (hl : l ≤ 0) :
    {p : Point n | 0 < p.2} ∩ (O ×ˢ Ioo l s) = O ×ˢ Ioo 0 s := by
  ext p
  constructor
  · intro hp
    exact ⟨hp.2.1, hp.1, hp.2.2.2⟩
  · intro hp
    exact ⟨hp.2.1, hp.1, hl.trans_lt hp.2.1, hp.2.2⟩

/-- Actual L2 data on the positive cylinder give actual L2 zero-past data on
 a cylinder crossing the initial face. -/
theorem zeroPast_memLp {n : ℕ} (O : Set (Space n)) {l s : ℝ} (hl : l ≤ 0)
    {u : Point n → ℝ} (hu : MemLp u 2 (productVolume O (Ioo 0 s))) :
    MemLp (zeroPast u) 2 (productVolume O (Ioo l s)) := by
  have hP : MeasurableSet {p : Point n | 0 < p.2} := isOpen_lt continuous_const continuous_snd |>.measurableSet
  rw [productVolume_eq_restrict] at hu ⊢
  rw [zeroPast, memLp_indicator_iff_restrict hP.nullMeasurableSet,
    Measure.restrict_restrict hP, zeroPast_positive_inter O hl]
  exact hu

theorem zeroPast_pairing_integral {n : ℕ} (O : Set (Space n)) {l s : ℝ} (hl : l ≤ 0)
    (u ψ : Point n → ℝ) :
    (∫ p, zeroPast u p * ψ p ∂productVolume O (Ioo l s)) =
      ∫ p, u p * ψ p ∂productVolume O (Ioo 0 s) := by
  have hP : MeasurableSet {p : Point n | 0 < p.2} := isOpen_lt continuous_const continuous_snd |>.measurableSet
  have he : (fun p => zeroPast u p * ψ p) = {p : Point n | 0 < p.2}.indicator (fun p => u p * ψ p) := by
    funext p
    by_cases hp : 0 < p.2
    · simp [zeroPast, hp]
    · simp [zeroPast, hp]
  rw [he, productVolume_eq_restrict, integral_indicator hP,
    Measure.restrict_restrict hP, zeroPast_positive_inter O hl, productVolume_eq_restrict]

end Yau.F04Proof

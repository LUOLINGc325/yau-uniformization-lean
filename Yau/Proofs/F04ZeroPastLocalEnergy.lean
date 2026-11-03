import Yau.Proofs.F04ZeroPastGradient

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem zeroPast_localEnergy {n : ℕ} {O : Set (Space n)} (hO : MeasurableSet O)
    {l s : ℝ} (hl : l ≤ 0) {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hu : MemLp u 2 (productVolume O (Ioo 0 s)))
    (hG : ∀ i, MemLp (fun p => G p i) 2 (productVolume O (Ioo 0 s)))
    (hWeak : WeakGradient O (Ioo 0 s) u G) :
    LocalEnergy O (Ioo l s) (zeroPast u) (fun p i => zeroPast (fun q => G q i) p) := by
  have hUE := zeroPast_memLp O hl hu
  have hGE := fun i => zeroPast_memLp O hl (hG i)
  refine ⟨zeroPast_weakGradient hO hl hu hG hWeak, ?_⟩
  intro V c e _hV _hVC hVO hI
  have hSub : V ×ˢ Ioo c e ⊆ O ×ˢ Ioo l s := fun p hp =>
    ⟨hVO (subset_closure hp.1), hI (Ioo_subset_Icc_self hp.2)⟩
  rw [productVolume_eq_restrict] at hUE hGE ⊢
  exact ⟨hUE.mono_measure (Measure.restrict_mono hSub le_rfl),
    fun i => (hGE i).mono_measure (Measure.restrict_mono hSub le_rfl)⟩

end Yau.F04Proof

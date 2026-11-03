import Yau.Proofs.F01NativeRestartMetricSmooth
import Yau.Proofs.F01ClosedMetricLowerOrder

/-! The original partial sandwich passes to the actual pasted terminal
metric by the proved metric-family continuity. -/
noncomputable section
open Set
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem pasted_terminal_metric_order
    (g K : HermitianField M) (h hR : ℝ → HermitianField M)
    {T ε C : ℝ} (hT : 0 < T) (hε : 0 < ε) (hR0 : hR 0 = K)
    (hSmooth : MetricFamilySmooth (nativePastedRestartFlow h hR T) (Icc 0 (T + ε / 2)))
    (hflow : ∀ x s, s ∈ Ico 0 T →
      (gMat (h s) x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
      ((C : ℂ) • gMat g x - gMat (h s) x).PosSemidef) :
    ∀ x, (gMat K x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
      ((C : ℂ) • gMat g x - gMat K x).PosSemidef := by
  have hClosed : MetricFamilySmooth (nativePastedRestartFlow h hR T) (Icc 0 T) := by
    intro a i j
    exact (hSmooth a i j).mono (prod_mono Subset.rfl
      (show Icc 0 T ⊆ Icc 0 (T + ε / 2) from fun s hs => ⟨hs.1, by linarith [hs.2]⟩))
  have hLower := closed_metric_lower_order_of_interior g (nativePastedRestartFlow h hR T)
    (c := C⁻¹) hT hClosed (fun x s hs => by
      simpa only [nativePastedRestartFlow, if_pos hs.2] using (hflow x s ⟨hs.1.le, hs.2⟩).1)
  have hUpper := closed_metric_upper_order_of_interior g (nativePastedRestartFlow h hR T)
    (C := C) hT hClosed (fun x s hs => by
      simpa only [nativePastedRestartFlow, if_pos hs.2] using (hflow x s ⟨hs.1.le, hs.2⟩).2)
  have hAt : nativePastedRestartFlow h hR T T = K := by
    simp only [nativePastedRestartFlow, lt_self_iff_false, ite_false, sub_self, hR0]
  intro x
  simpa only [hAt] using
    And.intro (hLower x T ⟨hT.le, le_rfl⟩) (hUpper x T ⟨hT.le, le_rfl⟩)

end Yau.NodeProofs.F01Aux

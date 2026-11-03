import Yau.Proofs.F01AInterfaces
import Yau.Proofs.F01PositiveHorizonNativeExtension

/-! The actual native terminal construction extends every genuine partial
potential solution. All clock maps and terminal pasting are supplied by the
released proved native extension theorem. -/
noncomputable section
open Set
open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem native_partial_solution_extends
    (g : HermitianField M) (hg : MetricSmooth g)
    (A : Yau.LeafProofs.L17Aux.BoundedChartFamily g)
    {Tstar : ℝ} (hTstar : 0 < Tstar)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ)
    (hpartial : NativePartialPotential g Tstar h U) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ hbar Ubar, NativePotentialSlab g (Tstar + ε) hbar Ubar ∧
        (∀ t ∈ Ico 0 Tstar, hbar t = h t) ∧
        (∀ x t, t ∈ Ico 0 Tstar → Ubar x t = U x t) := by
  rcases hpartial with ⟨h0, _, hU, hU0, ⟨C, hC, hData⟩, hpde⟩
  obtain ⟨Tnew, Cnew, hNew, V, hLong, hCnew, hNew0, hV0,
      hAgree, hMetric, hSmooth, hNewData⟩ :=
    exists_native_extension_of_positive_horizon g hg A hTstar hC h U hU hU0
      (fun t ht x => (hData x t ht).2.2) hpde
      (fun x t ht => ⟨(hData x t ht).1, (hData x t ht).2.1⟩)
  refine ⟨Tnew - Tstar, sub_pos.mpr hLong, hNew, V, ?_, ?_, ?_⟩
  · have hClock : Tstar + (Tnew - Tstar) = Tnew := by ring
    rw [hClock]
    exact ⟨hNew0.trans h0, hMetric, hSmooth, hV0, Cnew, hCnew, hNewData⟩
  · exact fun t ht => (hAgree t ht.2).1
  · exact fun x t ht => (hAgree t ht.2).2 x

end Yau.NodeProofs.F01Aux

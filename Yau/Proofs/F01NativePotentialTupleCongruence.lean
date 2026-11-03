import Yau.Proofs.F01NativePotentialTuple

/-! Exact agreement of native fields and potentials on the actual
closed interval preserves every genuine finite-tuple clause. -/
noncomputable section
open Set
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem NativePotentialTuple.congr
    {g : HermitianField M} {T C : ℝ} {h k : ℝ → HermitianField M}
    {U V : M.Carrier → ℝ → ℝ} (hTuple : NativePotentialTuple g T C h U) (hT : 0 ≤ T)
    (hFields : ∀ t ∈ Icc 0 T, h t = k t)
    (hValues : ∀ x t, t ∈ Icc 0 T → U x t = V x t) :
    NativePotentialTuple g T C k V := by
  obtain ⟨hC, hh0, hh, hU, hU0, hData⟩ := hTuple
  have ht0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  refine ⟨hC, (hFields 0 ht0).symm.trans hh0, ?_, ?_, ?_, ?_⟩
  · intro a i j
    apply (hh a i j).congr
    intro p hp
    rw [← hFields p.2 hp.2]
  · intro a
    exact (hU a).congr (fun p hp => (hValues (chartInv a p.1) p.2 hp.2).symm)
  · intro x
    exact (hValues x 0 ht0).symm.trans (hU0 x)
  · intro x t ht
    have hx := hData x t ht
    have hSlice : (fun y => U y t) = (fun y => V y t) := funext (fun y => hValues y t ht)
    have hIdentity := hx.2.2.1
    rw [hFields t ht, hSlice] at hIdentity
    have hPDE := hx.2.2.2.congr_of_mem (fun s hs => (hValues x s hs).symm) ht
    have hLog : flowLogDetRatio g h x t = flowLogDetRatio g k x t := by
      simp only [flowLogDetRatio, hFields t ht]
    refine ⟨?_, ?_, hIdentity, hPDE.congr_deriv hLog⟩
    · simpa only [hFields t ht] using hx.1
    · simpa only [hFields t ht] using hx.2.1

end Yau.NodeProofs.F01Aux

import Yau.Proofs.F01NativeRestartPaste

/-! The explicit native flow and potential paste retain the original
metric-potential identity on the complete extended interval. -/
noncomputable section
open Set
open scoped Matrix
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

def nativePastedRestartFlow (h hR : ℝ → HermitianField M) (T : ℝ) : ℝ → HermitianField M :=
  fun t => if t < T then h t else hR (t - T)

theorem nativePastedRestartPotential_before
    (U : M.Carrier → ℝ → ℝ) (u : M.Carrier → ℝ) (W : M.Carrier → ℝ → ℝ)
    (T : ℝ) (x : M.Carrier) {t : ℝ} (ht : t < T) :
    nativePastedRestartPotential U u W T x t = U x t := by
  simp only [nativePastedRestartPotential, if_pos ht.le, nativeClosedTerminalPotential, if_neg ht.ne]

theorem nativePastedRestartPotential_after
    (U : M.Carrier → ℝ → ℝ) (u : M.Carrier → ℝ) (W : M.Carrier → ℝ → ℝ)
    (T : ℝ) (hW0 : ∀ y, W y 0 = u y) (x : M.Carrier) {t : ℝ} (ht : T ≤ t) :
    nativePastedRestartPotential U u W T x t = W x (t - T) := by
  by_cases he : t = T
  · subst t
    simp only [nativePastedRestartPotential, le_refl, ite_true, nativeClosedTerminalPotential,
      sub_self, hW0]
  · have hn : ¬t ≤ T := fun hh => he (le_antisymm hh ht)
    exact if_neg hn

theorem nativePastedRestartFlow_potential_identity
    (g : HermitianField M) (h hR : ℝ → HermitianField M)
    (U : M.Carrier → ℝ → ℝ) (u : M.Carrier → ℝ) (W : M.Carrier → ℝ → ℝ)
    (T ε : ℝ) (hW0 : ∀ y, W y 0 = u y)
    (hpot : ∀ s ∈ Ico 0 T, ∀ y,
      gMat (h s) y = gMat g y - (s : ℂ) • ricci g y + levi (fun z => U z s) y)
    (hRpot : ∀ s ∈ Icc 0 ε, ∀ y,
      gMat (hR s) y = gMat g y - ((T + s : ℝ) : ℂ) • ricci g y + levi (fun z => W z s) y) :
    ∀ t ∈ Icc 0 (T + ε), ∀ x,
      gMat (nativePastedRestartFlow h hR T t) x =
        gMat g x - (t : ℂ) • ricci g x + levi (fun y => nativePastedRestartPotential U u W T y t) x := by
  intro t ht x
  by_cases hh : t < T
  · have he : (fun y => nativePastedRestartPotential U u W T y t) = (fun y => U y t) :=
      funext (fun y => nativePastedRestartPotential_before U u W T y hh)
    rw [he]
    simpa only [nativePastedRestartFlow, if_pos hh] using hpot t ⟨ht.1, hh⟩ x
  · have hTt : T ≤ t := le_of_not_gt hh
    have he : (fun y => nativePastedRestartPotential U u W T y t) = (fun y => W y (t - T)) :=
      funext (fun y => nativePastedRestartPotential_after U u W T hW0 y hTt)
    have hs : t - T ∈ Icc 0 ε := ⟨sub_nonneg.mpr hTt, by linarith [ht.2]⟩
    rw [he]
    have hClock : T + (t - T) = t := by ring
    simpa only [nativePastedRestartFlow, if_neg hh, hClock] using hRpot (t - T) hs x

end Yau.NodeProofs.F01Aux

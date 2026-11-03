import Yau.Proofs.F01ASameApproximationComparison
import Yau.Proofs.F01ANativeGlobalKahlerCore
import Yau.Proofs.F01FieldHeatPenalty

/-! Identify the first and second actual clock limits on the very same
subsequence. These lemmas retain the closed initial time face. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau

theorem actual_clock_derivative_eq_of_same_sequence_limits
    (f p : ℕ → ℝ → ℝ) (U : ℝ → ℝ) (P : ℝ)
    {H t : ℝ} (hH : 0 < H) (ht : t ∈ Icc 0 H)
    (hFirst : Tendsto (fun m => derivWithin (f m) (Icc 0 H) t) atTop
      (𝓝 (derivWithin U (Icc 0 H) t)))
    (hP : Tendsto (fun m => p m t) atTop (𝓝 P))
    (hFinite : ∀ᶠ m in atTop,
      HasDerivWithinAt (f m) (p m t) (Icc 0 H) t) :
    derivWithin U (Icc 0 H) t = P := by
  have hEq : ∀ᶠ m in atTop, derivWithin (f m) (Icc 0 H) t = p m t :=
    hFinite.mono (fun m hm => hm.derivWithin ((uniqueDiffOn_Icc hH) t ht))
  exact tendsto_nhds_unique hFirst (hP.congr' (hEq.mono (fun _ hm => hm.symm)))

theorem actual_hasDerivWithinAt_of_same_sequence_limits
    (f p : ℕ → ℝ → ℝ) (U : ℝ → ℝ) (P : ℝ)
    {H t : ℝ} (hH : 0 < H) (ht : t ∈ Icc 0 H)
    (hU : DifferentiableWithinAt ℝ U (Icc 0 H) t)
    (hFirst : Tendsto (fun m => derivWithin (f m) (Icc 0 H) t) atTop
      (𝓝 (derivWithin U (Icc 0 H) t)))
    (hP : Tendsto (fun m => p m t) atTop (𝓝 P))
    (hFinite : ∀ᶠ m in atTop,
      HasDerivWithinAt (f m) (p m t) (Icc 0 H) t) :
    HasDerivWithinAt U P (Icc 0 H) t := by
  rw [← actual_clock_derivative_eq_of_same_sequence_limits f p U P hH ht hFirst hP hFinite]
  exact hU.hasDerivWithinAt

theorem actual_second_clock_eq_derivWithin_of_pde
    (f p : ℝ → ℝ) {H t : ℝ} (hH : 0 < H) (ht : t ∈ Icc 0 H)
    (hpde : ∀ s ∈ Icc 0 H, HasDerivWithinAt f (p s) (Icc 0 H) s) :
    derivWithin (fun s => derivWithin f (Icc 0 H) s) (Icc 0 H) t =
      derivWithin p (Icc 0 H) t := by
  have hEq (s : ℝ) (hs : s ∈ Icc 0 H) : derivWithin f (Icc 0 H) s = p s :=
    (hpde s hs).derivWithin ((uniqueDiffOn_Icc hH) s hs)
  exact derivWithin_congr hEq (hEq t ht)

theorem actual_second_clock_nonpositive_of_inverse_square_caps
    (f : ℕ → ℝ → ℝ) (U : ℝ → ℝ) {L : ℕ → ℝ}
    (hL : Tendsto L atTop atTop) {H t a : ℝ}
    (hSecond : Tendsto
      (fun m => derivWithin (fun s => derivWithin (f m) (Icc 0 H) s) (Icc 0 H) t)
      atTop (𝓝 (derivWithin (fun s => derivWithin U (Icc 0 H) s) (Icc 0 H) t)))
    (hCap : ∀ᶠ m in atTop,
      derivWithin (fun s => derivWithin (f m) (Icc 0 H) s) (Icc 0 H) t ≤
        a / L m ^ 2) :
    derivWithin (fun s => derivWithin U (Icc 0 H) s) (Icc 0 H) t ≤ 0 :=
  nonpositive_of_eventual_inverse_square_cap hL hSecond hCap

theorem actual_derivWithin_nonpositive_of_second_clock_limit
    (f : ℕ → ℝ → ℝ) (U P : ℝ → ℝ) {L : ℕ → ℝ}
    (hL : Tendsto L atTop atTop) {H t a : ℝ} (ht : t ∈ Icc 0 H)
    (hFirst : ∀ s ∈ Icc 0 H, derivWithin U (Icc 0 H) s = P s)
    (hSecond : Tendsto
      (fun m => derivWithin (fun s => derivWithin (f m) (Icc 0 H) s) (Icc 0 H) t)
      atTop (𝓝 (derivWithin (fun s => derivWithin U (Icc 0 H) s) (Icc 0 H) t)))
    (hCap : ∀ᶠ m in atTop,
      derivWithin (fun s => derivWithin (f m) (Icc 0 H) s) (Icc 0 H) t ≤
        a / L m ^ 2) :
    derivWithin P (Icc 0 H) t ≤ 0 := by
  have hEq : derivWithin (fun s => derivWithin U (Icc 0 H) s) (Icc 0 H) t =
      derivWithin P (Icc 0 H) t :=
    derivWithin_congr hFirst (hFirst t ht)
  rw [← hEq]
  exact actual_second_clock_nonpositive_of_inverse_square_caps f U hL hSecond hCap

theorem actual_derivWithin_Ici_eq_Icc
    (P : ℝ → ℝ) {H t : ℝ} (ht : 0 ≤ t) (hT : t < H)
    (hP : DifferentiableWithinAt ℝ P (Ici 0) t) :
    derivWithin P (Ici 0) t = derivWithin P (Icc 0 H) t := by
  have hd := hasDerivWithinAt_Ici_of_Icc ht hT
    (hP.mono (fun s hs => hs.1)).hasDerivWithinAt
  exact hd.derivWithin ((uniqueDiffOn_Ici 0) t ht)

end Yau.NodeProofs.F01Aux

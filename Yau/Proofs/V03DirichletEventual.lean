import Yau.Proofs.V03DirichletContinuity

/-! The native Hilbert continuity result only needs eventual regularity of
the varying traces; values outside that eventual set do not affect the limit. -/

open scoped Topology
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem boundaryDSq_toReal_tendsto_of_eventual_sub {α : Type*} {l : Filter α}
    (U : α → ℝ → ℂ) (u : ℝ → ℂ)
    (hU : ∀ᶠ a in l, Continuous (U a) ∧ boundaryDSq (fun θ (_ : Unit) => U a θ) ≠ ⊤)
    (hu : Continuous u) (huf : boundaryDSq (fun θ (_ : Unit) => u θ) ≠ ⊤)
    (hsub : Tendsto (fun a =>
      (boundaryDSq (fun θ (_ : Unit) => U a θ - u θ)).toReal) l (𝓝 (0 : ℝ))) :
    Tendsto (fun a => (boundaryDSq (fun θ (_ : Unit) => U a θ)).toReal) l
      (𝓝 (boundaryDSq (fun θ (_ : Unit) => u θ)).toReal) := by
  classical
  let good : α → Prop := fun a => Continuous (U a) ∧
    boundaryDSq (fun θ (_ : Unit) => U a θ) ≠ ⊤
  let W : α → ℝ → ℂ := fun a => if good a then U a else u
  have hWC (a : α) : Continuous (W a) := by
    by_cases ha : good a
    · simpa only [W, if_pos ha] using ha.1
    · simpa only [W, if_neg ha] using hu
  have hWF (a : α) : boundaryDSq (fun θ (_ : Unit) => W a θ) ≠ ⊤ := by
    by_cases ha : good a
    · simpa only [W, if_pos ha] using ha.2
    · simpa only [W, if_neg ha] using huf
  have heq : W =ᶠ[l] U := hU.mono fun a ha => if_pos ha
  have hs : Tendsto (fun a =>
      (boundaryDSq (fun θ (_ : Unit) => W a θ - u θ)).toReal) l (𝓝 (0 : ℝ)) :=
    hsub.congr' (heq.mono fun a ha => congrArg
      (fun v : ℝ → ℂ => (boundaryDSq (fun θ (_ : Unit) => v θ - u θ)).toReal) ha.symm)
  have ht := boundaryDSq_toReal_tendsto_of_sub W u hWC hu hWF huf hs
  apply ht.congr'
  filter_upwards [heq] with a ha
  rw [ha]

end Yau.Blueprint.V03Proof

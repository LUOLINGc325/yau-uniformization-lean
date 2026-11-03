import Yau.Proofs.F05SmoothContinuity
import Yau.Proofs.F05FlowBarriers

/-! On a fixed compact spatial set the actual rho barrier supplies one
amplitude budget before every approximant and its exhaustion domain. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Blueprint
variable {n : ℕ} {X : KahlerManifold n}

theorem F05_flow_compact_rho_budget (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (T : ℝ) {K : Set (Pt X)} (hK : IsCompact K) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ K, ∀ t ∈ Icc 0 T, ρ x t+2 ≤ B := by
  have hCont := F05_smooth_spacetime_continuousOn hloc.2.2.2.1
  have hSub : K ×ˢ Icc (0 : ℝ) T ⊆ (univ : Set (Pt X)) ×ˢ Ici 0 :=
    fun z hz => ⟨mem_univ _,hz.2.1⟩
  obtain ⟨C,hC⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn (hCont.mono hSub)
  refine ⟨1+|C|+2,by positivity,?_⟩
  intro x hx t ht
  have hBound : |ρ x t| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC (x,t) ⟨hx,ht⟩
  linarith [le_abs_self (ρ x t),le_abs_self C]

end Yau.Proofs.F05Aux

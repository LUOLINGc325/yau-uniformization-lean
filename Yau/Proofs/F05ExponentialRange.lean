import Yau.Proofs.F05FlowClassicalBarriers

/-! The actual barriers give one positive q=exp(w) value range before all
moving endpoints and all candidate solutions, independently of gradients. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.Blueprint Yau.F05Transport
variable {n : ℕ} {X : KahlerManifold n}

theorem F05_exp_barrier_uniform {O : Set (Pt X)} {A : AtlasData X.manifold}
    (hA : GenuineAtlas O A) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (S a : ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (T : ℝ), T ≤ S → ∀ w : STF X,
      (∀ x ∈ closure O, ∀ t ∈ Icc 0 T, 0 ≤ w x t ∧ w x t ≤ ρ x t+2*a) →
      ∀ x ∈ closure O, ∀ t ∈ Icc 0 T, 1 ≤ Real.exp (w x t) ∧ Real.exp (w x t) ≤ B := by
  have hρ : SmoothSpaceTime ρ (Icc 0 S) := fun x => (hloc.2.2.2.1 x).mono (fun q hq => ⟨hq.1,hq.2.1⟩)
  obtain ⟨C,hC⟩ := ((F05_atlas_closure_compact hA).prod isCompact_Icc).exists_bound_of_continuousOn
    ((F05_smooth_spacetime_continuousOn hρ).mono (fun q hq => ⟨mem_univ _,hq.2⟩))
  let D := 1+|C|+2*|a|
  refine ⟨Real.exp D,Real.one_le_exp_iff.mpr (by dsimp only [D]; positivity),?_⟩
  intro T hTS w hw x hx t ht
  have hAt := hw x hx t ht
  have hρBound : |ρ x t| ≤ C := hC (x,t) ⟨hx,ht.1,ht.2.trans hTS⟩
  refine ⟨Real.one_le_exp_iff.mpr hAt.1,Real.exp_le_exp.mpr ?_⟩
  dsimp only [D]
  linarith [le_abs_self (ρ x t),le_abs_self C,le_abs_self a]

end Yau.Proofs.F05Aux

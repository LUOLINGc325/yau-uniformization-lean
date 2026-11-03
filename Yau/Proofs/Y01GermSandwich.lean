import Yau.Proofs.Y01CoordinateGerms

/-! Small composition lemmas keep finite-jet substitutions opaque when
assembling the two coordinate changes around a geometric transition. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint
open scoped ContDiff

variable {n d : ℕ}

theorem germJetEq_of_function_eq
    {f g f' g' : ComplexVector n → ComplexVector n}
    (hf : f = f') (hg : g = g') (h : GermJetEq f g d) : GermJetEq f' g' d := by
  subst f'
  subst g'
  exact h

theorem germJetEq_sandwich
    {f g left right : ComplexVector n → ComplexVector n}
    (hf : ContDiffAt ℂ d f 0) (hg : ContDiffAt ℂ d g 0)
    (hleft : ContDiffAt ℂ d left 0) (hright : ContDiffAt ℂ d right 0)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (hright0 : right 0 = 0)
    (hfg : GermJetEq f g d) :
    GermJetEq (left ∘ f ∘ right) (left ∘ g ∘ right) d := by
  have hfr : ContDiffAt ℂ d (f ∘ right) 0 := contDiffAt_comp_zero hright hf hright0
  have hgr : ContDiffAt ℂ d (g ∘ right) 0 := contDiffAt_comp_zero hright hg hright0
  have hfr0 : (f ∘ right) 0 = 0 := by simp only [Function.comp_apply, hright0, hf0]
  have hgr0 : (g ∘ right) 0 = 0 := by simp only [Function.comp_apply, hright0, hg0]
  have h := germJetEq_comp hright hright hf hg hright0 hright0
    (germJetEq_refl right d) hfg
  simpa only [Function.comp_assoc] using
    germJetEq_comp hfr hgr hleft hleft hfr0 hgr0 h (germJetEq_refl left d)

theorem germ_coordinate_transition_congr
    {F outer outer' inner inner' : ComplexVector n → ComplexVector n}
    (hF : ContDiffAt ℂ d F 0) (hF0 : F 0 = 0)
    (ho : ContDiffAt ℂ d outer 0) (ho' : ContDiffAt ℂ d outer' 0)
    (hi : ContDiffAt ℂ d inner 0) (hi' : ContDiffAt ℂ d inner' 0)
    (hi0 : inner 0 = 0) (hi'0 : inner' 0 = 0)
    (houter : GermJetEq outer outer' d) (hinner : GermJetEq inner inner' d) :
    GermJetEq (outer ∘ F ∘ inner) (outer' ∘ F ∘ inner') d := by
  have hfi : ContDiffAt ℂ d (F ∘ inner) 0 := contDiffAt_comp_zero hi hF hi0
  have hfi' : ContDiffAt ℂ d (F ∘ inner') 0 := contDiffAt_comp_zero hi' hF hi'0
  have hfi0 : (F ∘ inner) 0 = 0 := by simp only [Function.comp_apply, hi0, hF0]
  have hfi'0 : (F ∘ inner') 0 = 0 := by simp only [Function.comp_apply, hi'0, hF0]
  have h := germJetEq_comp hi hi' hF hF hi0 hi'0 hinner (germJetEq_refl F d)
  simpa only [Function.comp_assoc] using
    germJetEq_comp hfi hfi' ho ho' hfi0 hfi'0 h houter

end Yau.Proofs.Y01Aux

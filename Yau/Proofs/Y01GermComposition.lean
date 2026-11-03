import Yau.Geometry.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Finite equality of the actual iterated Fréchet derivatives is stable
under smooth composition at zero. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open scoped ContDiff

variable {n d : ℕ}

theorem taylorComp_congr_through
    {p p' q q' : FormalMultilinearSeries ℂ (ComplexVector n) (ComplexVector n)}
    (hp : ∀ m ≤ d, p m = p' m) (hq : ∀ m ≤ d, q m = q' m)
    {m : ℕ} (hm : m ≤ d) : q.taylorComp p m = q'.taylorComp p' m := by
  unfold FormalMultilinearSeries.taylorComp
  apply Finset.sum_congr rfl
  intro c hc
  unfold FormalMultilinearSeries.compAlongOrderedFinpartition
  rw [hq c.length (c.length_le.trans hm)]
  congr 1
  funext j
  exact hp (c.partSize j) ((c.partSize_le j).trans hm)

theorem germJetEq_comp
    {f f' g g' : ComplexVector n → ComplexVector n}
    (hf : ContDiffAt ℂ d f 0) (hf' : ContDiffAt ℂ d f' 0)
    (hg : ContDiffAt ℂ d g 0) (hg' : ContDiffAt ℂ d g' 0)
    (hf0 : f 0 = 0) (hf'0 : f' 0 = 0)
    (hff' : GermJetEq f f' d) (hgg' : GermJetEq g g' d) :
    GermJetEq (g ∘ f) (g' ∘ f') d := by
  intro m hm
  have hgF : ContDiffAt ℂ d g (f 0) := by simpa only [hf0] using hg
  have hgF' : ContDiffAt ℂ d g' (f' 0) := by simpa only [hf'0] using hg'
  rw [iteratedFDeriv_comp hgF hf (by exact_mod_cast hm),
    iteratedFDeriv_comp hgF' hf' (by exact_mod_cast hm), hf0, hf'0]
  exact taylorComp_congr_through hff' hgg' hm

theorem germJetEq_refl (f : ComplexVector n → ComplexVector n) (d : ℕ) :
    GermJetEq f f d := fun _ _ => rfl

theorem germJetEq_symm {f g : ComplexVector n → ComplexVector n}
    (h : GermJetEq f g d) : GermJetEq g f d := fun m hm => (h m hm).symm

theorem germJetEq_trans {f g h : ComplexVector n → ComplexVector n}
    (hfg : GermJetEq f g d) (hgh : GermJetEq g h d) : GermJetEq f h d :=
  fun m hm => (hfg m hm).trans (hgh m hm)

end Yau.Proofs.Y01Aux

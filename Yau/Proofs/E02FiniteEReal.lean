import Yau.Blueprint.Nodes

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.NodeProofs.E02Aux

/-- A genuine finite upper bound and nonnegativity rule out both
infinities before any evaluation by EReal.toReal. -/
theorem nonnegative_ereal_finite_bounds (a : EReal) (C : ℝ)
    (h0 : 0 ≤ a) (hC : a ≤ (C : EReal)) :
    a ≠ ⊤ ∧ a ≠ ⊥ ∧ (a.toReal : EReal) = a ∧ 0 ≤ a.toReal ∧ a.toReal ≤ C := by
  have hTop : a ≠ ⊤ := ne_of_lt (hC.trans_lt (by simp))
  have hBot : a ≠ ⊥ := ne_of_gt ((by simp : (⊥ : EReal) < 0).trans_le h0)
  have hCoe : (a.toReal : EReal) = a := EReal.coe_toReal hTop hBot
  refine ⟨hTop,hBot,hCoe,?_,?_⟩
  · apply EReal.coe_nonneg.mp
    rw [hCoe]
    exact h0
  · apply EReal.coe_le_coe_iff.mp
    rw [hCoe]
    exact hC

theorem lowerSemicontinuousOn_ereal_toReal {D : Type*} [TopologicalSpace D]
    (f : D → EReal) (S : Set D) (hf : LowerSemicontinuousOn f S)
    (hTop : ∀ x ∈ S, f x ≠ ⊤) (hBot : ∀ x ∈ S, f x ≠ ⊥) :
    LowerSemicontinuousOn (fun x => (f x).toReal) S := by
  intro x hx r hr
  have hCoe : ((f x).toReal : EReal) = f x := EReal.coe_toReal (hTop x hx) (hBot x hx)
  have hrE : (r : EReal) < f x := by
    rw [←hCoe]
    exact EReal.coe_lt_coe_iff.mpr hr
  have hNear := hf x hx (r : EReal) hrE
  filter_upwards [hNear,self_mem_nhdsWithin] with y hy hDom
  apply EReal.coe_lt_coe_iff.mp
  rw [EReal.coe_toReal (hTop y hDom) (hBot y hDom)]
  exact hy

end Yau.NodeProofs.E02Aux

import Yau.Proofs.F05BootstrapRegions

/-! Good derivatives are actual line derivatives. Tangent lines stay on the
physical side, and their derivatives agree with the computed spatial jets.
The commutator order bound is finite and independent of any smoothness claim. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem F05GoodWord_append (T : ℝ) (β γ : List (Option (RIdx n))) (f : Point n → V) :
    F05GoodWord T (β++γ) f = F05GoodWord T β (F05GoodWord T γ f) := by
  induction β with
  | nil => rfl
  | cons a β ih => simp only [List.cons_append,F05GoodWord,ih]

theorem F05GoodList_cons (ν a : Option (RIdx n)) (β : List (Option (RIdx n))) :
    F05GoodList ν (a::β) ↔ F05GoodLetter ν a ∧ F05GoodList ν β := by
  simp only [F05GoodList,List.mem_cons,forall_eq_or_imp]

theorem F05GoodList_commutator_order
    {β : List (Option (RIdx n))} {st : List (Option (RIdx n)) × List (Option (RIdx n))}
    (hst : st ∈ commutatorSplits β) : st.1 ≠ [] ∧ st.2.length+1 ≤ β.length :=
  ⟨(commutatorSplits_properties β st hst).1,commutatorSplits_lower_length β st hst⟩

theorem F05_good_line_mem_region {ν : Option (RIdx n)} {k : RIdx n}
    (hk : F05GoodLetter ν (some k)) {x : Space n} {r : ℝ}
    (hx : x ∈ region ν r) (hxr : ‖x‖ < r) :
    ∀ᶠ a : ℝ in 𝓝 0, x+a • realVec k ∈ region ν r := by
  have hNear : {a : ℝ | ‖x+a • realVec k‖ < r} ∈ 𝓝 0 := by
    apply (isOpen_lt ((continuous_const.add
      (continuous_id.smul continuous_const)).norm) continuous_const).mem_nhds
    change ‖x+(0 : ℝ) • realVec k‖ < r
    simpa only [zero_smul,add_zero] using hxr
  filter_upwards [hNear] with a ha
  refine ⟨ha.le,?_⟩
  cases ν with
  | none => trivial
  | some j =>
    have hkj : k ≠ j := hk
    have hVec : realCoord (realVec k) j = 0 := by
      rw [← real_inner_realVec,realVec_inner,if_neg hkj]
    have hCoord : realCoord (x+a • realVec k) j = realCoord x j := by
      rw [← realCoordLinear_apply, map_add, map_smul]
      simp only [realCoordLinear_apply,smul_eq_mul]
      rw [hVec]
      ring
    change realCoord (x+a • realVec k) j ≤ 0
    rw [hCoord]
    exact hx.2

theorem F05_good_spatial_partial_eq_relD {X : Set (Space n)} {T : ℝ}
    {f : Point n → V} {z : Point n} (k : RIdx n)
    (hf : DifferentiableWithinAt ℝ (fun x => f (x,z.2)) X z.1)
    (hLine : ∀ᶠ a : ℝ in 𝓝 0, z.1+a • realVec k ∈ X) :
    F05GoodPartial T (some k) f z = F05RelD X f z (realVec k) := by
  have hDeriv : HasDerivAt (fun a : ℝ => z.1+a • realVec k) (realVec k) 0 := by
    simpa only [id_eq,one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (realVec k)).const_add z.1
  have h := hf.hasFDerivWithinAt.comp_hasDerivAt_of_eq 0 hDeriv hLine
    (by simp only [zero_smul,add_zero])
  exact h.deriv

theorem F05_good_spatial_diff {X : Set (Space n)} {T : ℝ}
    {f : Point n → V} {z : Point n} (k : RIdx n)
    (hf : DifferentiableWithinAt ℝ (fun x => f (x,z.2)) X z.1)
    (hLine : ∀ᶠ a : ℝ in 𝓝 0, z.1+a • realVec k ∈ X) :
    DifferentiableAt ℝ (fun a : ℝ => f (z.1+a • realVec k,z.2)) 0 := by
  have hDeriv : HasDerivAt (fun a : ℝ => z.1+a • realVec k) (realVec k) 0 := by
    simpa only [id_eq,one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (realVec k)).const_add z.1
  exact (hf.hasFDerivWithinAt.comp_hasDerivAt_of_eq 0 hDeriv hLine
    (by simp only [zero_smul,add_zero])).differentiableAt

end Yau.Proofs.F05Aux

import Yau.Proofs.G04

/-! The actual zero form is a bounded solution of the computed Hodge heat equation. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff ComplexOrder
namespace Yau.Proofs.F03Aux
open Yau Blueprint LeafProofs
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem isBoundedFormHeat_zero (g : HermitianField M) (k : ℕ) :
    IsBoundedFormHeat g (0 : RealForm M k) (fun _ => 0) := by
  refine ⟨?_,⟨rfl,?_⟩,?_,?_⟩
  · intro x I
    simpa only [L03.formComponents_zero,Pi.zero_apply] using
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ComplexVector n × ℝ => (0:ℝ)) (chartTarget x ×ˢ Ioi 0))
  · intro x K _hK _hKt j I ε hε
    refine ⟨1,zero_lt_one,fun t _ht _ht1 z _hz => ?_⟩
    simpa [L03.formComponents_zero] using hε
  · intro T _hT
    refine ⟨1,zero_lt_one,fun x t _ht _htT => ?_⟩
    simp [formNormSq,L03.formInner_zero_left]
  · intro x z _hz t _ht I
    simpa only [L03.formComponents_zero,Pi.zero_apply,hodgeGeneratorComponents,
      L03.hodgeComponents_zero,neg_zero,zero_div] using hasDerivAt_const t (0:ℝ)

theorem boundedOneOneData_zero (g : HermitianField M) :
    BoundedOneOneData g (0 : RealForm M 2) := by
  refine ⟨L03.smoothRealForm_zero,?_,0,le_rfl,?_⟩
  · intro x u v
    simp
  · intro x
    have hzero : formHermitianMatrix (0 : RealForm M 2) x=0 := by
      ext a b
      simp [formHermitianMatrix]
    simp only [hzero,neg_zero,Complex.ofReal_zero,zero_smul,sub_zero,zero_sub]
    exact ⟨Matrix.PosSemidef.zero,Matrix.PosSemidef.zero⟩

theorem formLE_zero_iff (A : RealForm M 2) :
    FormLE (0 : RealForm M 2) A ↔ ∀ x,(formHermitianMatrix A x).PosSemidef := by
  have hzero (x : M.Carrier) : formHermitianMatrix (0 : RealForm M 2) x=0 := by
    ext a b
    simp [formHermitianMatrix]
  simp only [FormLE,hzero,sub_zero]

theorem hodgeHeat_nonnegative_of_registered_order
    (g : HermitianField M) (hOrder : HodgeTypeAndOrder g)
    (A : RealForm M 2) (U : ℝ → RealForm M 2)
    (hA : BoundedOneOneData g A) (hU : IsBoundedFormHeat g A U)
    (hA0 : ∀ x,(formHermitianMatrix A x).PosSemidef) {t : ℝ} (ht : 0 < t) :
    ∀ x,(formHermitianMatrix (U t) x).PosSemidef := by
  exact (formLE_zero_iff (U t)).mp (hOrder.2.1 0 A (fun _ => 0) U
    (boundedOneOneData_zero g) hA (isBoundedFormHeat_zero g 2) hU
    ((formLE_zero_iff A).mpr hA0) t ht)

end Yau.Proofs.F03Aux

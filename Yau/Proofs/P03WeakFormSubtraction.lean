import Yau.Proofs.P03WeakTopRepresentative
import Yau.LeafProofs.L14

open scoped Manifold Topology ContDiff
open Set Filter MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar Yau.LeafProofs.L14Aux

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem subForm_eq_add_smul {q : ℕ} (u v : NQForm E q) :
    subForm E u v = u + (-1 : ℂ) • v := by
  funext x
  apply Subtype.ext
  ext w t
  change (u x).1 w t - (v x).1 w t = (u x).1 w t + (-1 : ℂ) • (v x).1 w t
  simp only [neg_one_smul, sub_eq_add_neg]

theorem coefficients_subForm {q : ℕ} (u v : NQForm E q)
    (a : M.Carrier) (z : ComplexVector n) (I : Fin q → Fin n) (α : Fin r) :
    coefficients (r := r) E (subForm E u v) a z I α =
      coefficients (r := r) E u a z I α - coefficients (r := r) E v a z I α := by
  rw [subForm_eq_add_smul, coefficients_add, coefficients_smul]
  ring

theorem locallyL2_subForm {q : ℕ} (u v : NQForm E q)
    (hu : LocallyL2 (r := r) E u) (hv : LocallyL2 (r := r) E v) :
    LocallyL2 (r := r) E (subForm E u v) := by
  rw [subForm_eq_add_smul]
  exact locallyL2_add E u ((-1 : ℂ) • v) hu (locallyL2_smul E (-1) v hv)

theorem locallyL2_mul_compact_test_integrable {q : ℕ}
    (u : NQForm E q) (hu : LocallyL2 (r := r) E u)
    (a : M.Carrier) (I : Fin q → Fin n) (α : Fin r)
    (ψ : ComplexVector n → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ localDomain (r := r) E a) :
    Integrable (fun z => coefficients (r := r) E u a z I α * ψ z) (lebesgueC n) := by
  have hp : IntegrableOn (fun z => coefficients (r := r) E u a z I α * ψ z)
      (tsupport ψ) (lebesgueC n) :=
    test_mul_integrable_of_memLp ((lebesgueC n).restrict (tsupport ψ)) _ ψ
      (Yau.LeafProofs.L14Aux.locallyL2_coefficients_memLp E u hu a I α (tsupport ψ) hc hs)
      (compact_test_memLp ψ hψ hc (tsupport ψ))
  exact (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right _ _).trans (subset_tsupport ψ))).mp hp

/-- Subtraction preserves the original distributional tests; the two
equal source integrals cancel after integrability has been established. -/
theorem weakDbar_subForm_same_source (u v : NQForm E 0) (f : NQForm E 1)
    (hu : WeakDbar (r := r) E u f) (hv : WeakDbar (r := r) E v f) :
    WeakDbar (r := r) E (subForm E u v) (zeroForm E 1) := by
  apply (weakDbar_zero_iff_component_tests E _ _).mpr
  refine ⟨locallyL2_subForm E u v hu.1 hv.1, locallyL2_zero E 1, ?_⟩
  intro a i α ψ hψ hc hs
  have ht := (weakDbar_zero_iff_component_tests E u f).mp hu |>.2.2 a i α ψ hψ hc hs
  have ht' := (weakDbar_zero_iff_component_tests E v f).mp hv |>.2.2 a i α ψ hψ hc hs
  have heq := neg_injective (ht.symm.trans ht')
  have hsc : tsupport (fun z => wirtBar ψ z (stdVec i)) ⊆ tsupport ψ :=
    closure_minimal (support_wirtBar_subset ψ (stdVec i)) (isClosed_tsupport ψ)
  have htest := (wirtBar_contDiff ψ hψ (stdVec i)).continuous
  have hcomp := wirtBar_hasCompactSupport ψ hc (stdVec i)
  have hiu := locallyL2_mul_compact_test_integrable E u hu.1 a Fin.elim0 α _ htest hcomp (hsc.trans hs)
  have hiv := locallyL2_mul_compact_test_integrable E v hv.1 a Fin.elim0 α _ htest hcomp (hsc.trans hs)
  simp only [coefficients_zeroForm, PiLp.zero_apply, zero_mul, integral_zero,
    coefficients_subForm, sub_mul]
  rw [integral_sub hiu hiv, heq, sub_self, neg_zero]

theorem subForm_subForm_cancel (u v : NQForm E 0) :
    subForm E u (subForm E u v) = v := by
  funext x
  apply Subtype.ext
  change (u x).1 - ((u x).1 - (v x).1) = (v x).1
  abel

end Yau.NodeProofs.P03Aux

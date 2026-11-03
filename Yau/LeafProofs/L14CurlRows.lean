import Yau.LeafProofs.L14CurlSystem

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix
open MeasureTheory Bundle Filter Module

namespace Yau.LeafProofs.L14Aux
open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem locallyL2_test_integrable {q : ℕ}
    (u : NQForm E q) (hu : LocallyL2 (r := r) E u)
    (a : M.Carrier) (I : Fin q → Fin n) (α : Fin r)
    (ψ : ComplexVector n → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ localDomain (r := r) E a) :
    Integrable (fun z => coefficients (r := r) E u a z I α * ψ z) (lebesgueC n) := by
  have hp : IntegrableOn (fun z => coefficients (r := r) E u a z I α * ψ z)
      (tsupport ψ) (lebesgueC n) :=
    test_mul_integrable_of_memLp ((lebesgueC n).restrict (tsupport ψ)) _ ψ
      (locallyL2_coefficients_memLp E u hu a I α (tsupport ψ) hc hs)
      (compact_test_memLp ψ hψ hc (tsupport ψ))
  exact (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right _ _).trans (subset_tsupport ψ))).mp hp

theorem weakDbar_complex_firstOrder_curl_rows
    (u : NQForm E 1) (f : NQForm E 2) (huf : WeakDbar (r := r) E u f)
    (a : M.Carrier) (k : (Fin n × Fin n) × Fin r) (ψ : ComplexVector n → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ localDomain (r := r) E a) :
    (∫ z, (ψ z : ℂ) * coefficients (r := r) E f a z ![k.1.1,k.1.2] k.2 ∂lebesgueC n) =
      ∫ z, ∑ c : Fin n × Fin r, coefficients (r := r) E u a z (fun _ => c.1) c.2 *
        (-(∑ p : RIdx n,
          (curlFirstOrderDerivative k c p z * (fderiv ℝ ψ z (realVec p) : ℂ) +
          fderiv ℝ (curlFirstOrderDerivative k c p) z (realVec p) * (ψ z : ℂ))) +
          curlFirstOrderValue k c z * (ψ z : ℂ)) ∂lebesgueC n := by
  classical
  let ψC := fun z => Complex.ofReal (ψ z)
  have hψC : ContDiff ℝ ∞ ψC := Complex.ofRealCLM.contDiff.comp hψ
  have hcψC : HasCompactSupport ψC := hc.comp_left Complex.ofReal_zero
  have hsψC : tsupport ψC ⊆ localDomain (r := r) E a :=
    (tsupport_comp_subset Complex.ofReal_zero ψ).trans hs
  have hD (i : Fin n) : ContDiff ℝ ∞ (fun z => wirtBar ψC z (stdVec i)) := by
    simpa only [contDiffOn_univ] using wirtBar_contDiffOn isOpen_univ _ hψC.contDiffOn (stdVec i)
  have hsD (i : Fin n) : tsupport (fun z => wirtBar ψC z (stdVec i)) ⊆ tsupport ψC :=
    closure_minimal (support_wirtBar_subset ψC (stdVec i)) (isClosed_tsupport _)
  have hInt (i j : Fin n) : Integrable (fun z => coefficients (r := r) E u a z (fun _ => i) k.2 *
      wirtBar ψC z (stdVec j)) (lebesgueC n) :=
    locallyL2_test_integrable E u huf.1 a (fun _ => i) k.2 _ (hD j).continuous
      (hcψC.of_isClosed_subset (isClosed_tsupport _) (hsD j)) ((hsD j).trans hsψC)
  have he := weakDbar_one_component_tests E u f huf a k.1.1 k.1.2 k.2 ψC hψC hcψC hsψC
  have hpoint (z : ComplexVector n) :
      (∑ c : Fin n × Fin r, coefficients (r := r) E u a z (fun _ => c.1) c.2 *
        (-(∑ p : RIdx n,
          (curlFirstOrderDerivative k c p z * (fderiv ℝ ψ z (realVec p) : ℂ) +
          fderiv ℝ (curlFirstOrderDerivative k c p) z (realVec p) * (ψ z : ℂ))) +
          curlFirstOrderValue k c z * (ψ z : ℂ))) =
      -(coefficients (r := r) E u a z (fun _ => k.1.2) k.2 * wirtBar ψC z (stdVec k.1.1)) +
        coefficients (r := r) E u a z (fun _ => k.1.1) k.2 * wirtBar ψC z (stdVec k.1.2) := by
    simp_rw [curlFirstOrder_formal_test_row k _ ψ z (hψ.differentiable (by simp) z)]
    simp only [mul_add, mul_neg, mul_ite, mul_zero, Finset.sum_add_distrib,
      Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rfl
  have hIntegral : (∫ z,
      -(coefficients (r := r) E u a z (fun _ => k.1.2) k.2 * wirtBar ψC z (stdVec k.1.1)) +
        coefficients (r := r) E u a z (fun _ => k.1.1) k.2 * wirtBar ψC z (stdVec k.1.2) ∂lebesgueC n) =
      -(∫ z, coefficients (r := r) E u a z (fun _ => k.1.2) k.2 * wirtBar ψC z (stdVec k.1.1) ∂lebesgueC n) +
        ∫ z, coefficients (r := r) E u a z (fun _ => k.1.1) k.2 * wirtBar ψC z (stdVec k.1.2) ∂lebesgueC n := by
    simpa only [Pi.neg_apply, integral_neg] using integral_add (hInt k.1.2 k.1.1).neg (hInt k.1.1 k.1.2)
  calc
    _ = ∫ z, coefficients (r := r) E f a z ![k.1.1,k.1.2] k.2 * ψC z ∂lebesgueC n :=
      integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
    _ = _ := he
    _ = _ := hIntegral.symm
    _ = _ := integral_congr_ae (Eventually.of_forall fun z => (hpoint z).symm)

end Yau.LeafProofs.L14Aux

import Yau.LeafProofs.L10InteriorCalculus

/-! Compactly supported tests require smoothness only on the original open ball. -/

noncomputable section
open MeasureTheory
open scoped ContDiff Topology

namespace Yau.LeafProofs

theorem elliptic_contDiffOn_directionalDerivative {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : ComplexVector n → F} {O : Set (ComplexVector n)}
    (hO : IsOpen O) (hu : ContDiffOn ℝ ∞ u O) (e : ComplexVector n) :
    ContDiffOn ℝ ∞ (fun x => fderiv ℝ u x e) O := by
  intro x hx
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ u) x :=
    (hu.contDiffAt (hO.mem_nhds hx)).fderiv_right (by simp)
  exact (hD.clm_apply contDiffAt_const).contDiffWithinAt

theorem elliptic_contDiff_mul_of_tsupport_subset {n : ℕ}
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    {φ u : ComplexVector n → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hs : tsupport φ ⊆ O) (hu : ContDiffOn ℝ ∞ u O) :
    ContDiff ℝ ∞ (fun x => φ x * u x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport φ
  · exact hφ.contDiffAt.mul (hu.contDiffAt (hO.mem_nhds (hs hx)))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp [hy]

theorem elliptic_local_test_product_integrable {n : ℕ}
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    {φ u : ComplexVector n → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ) (hs : tsupport φ ⊆ O)
    (hu : ContDiffOn ℝ ∞ u O) : Integrable (fun x => φ x * u x) volume :=
  (elliptic_contDiff_mul_of_tsupport_subset hO hφ hs hu).continuous
    |>.integrable_of_hasCompactSupport hcφ.mul_right

theorem elliptic_local_test_integration_by_parts {n : ℕ}
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    {φ u : ComplexVector n → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ) (hs : tsupport φ ⊆ O)
    (hu : ContDiffOn ℝ ∞ u O) (e : ComplexVector n) :
    (∫ x, φ x * fderiv ℝ u x e ∂lebesgueC n) =
      -(∫ x, fderiv ℝ φ x e * u x ∂lebesgueC n) := by
  rw [lebesgueC_eq_volume]
  have hDφ : ContDiff ℝ ∞ (fun x => fderiv ℝ φ x e) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (elliptic_local_test_product_integrable hO hDφ (hcφ.fderiv_apply ℝ e)
      ((tsupport_fderiv_apply_subset ℝ e).trans hs) hu)
    (elliptic_local_test_product_integrable hO hφ hcφ hs
      (elliptic_contDiffOn_directionalDerivative hO hu e))
    (elliptic_local_test_product_integrable hO hφ hcφ hs hu)
    (fun x _ => (hφ.differentiable (by simp)).differentiableAt)
    (fun x hx => (hu.contDiffAt (hO.mem_nhds (hs hx))).differentiableAt (by simp))

def ellipticFlux {n : ℕ}
    (a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    (u : ComplexVector n → ℂ) (i : RIdx n) (z : ComplexVector n) : ℂ :=
  ∑ j, (a z i j : ℂ) * fderiv ℝ u z (realVec j)

theorem ellipticFlux_contDiffOn {n : ℕ}
    {a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ}
    {u : ComplexVector n → ℂ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) O)
    (hu : ContDiffOn ℝ ∞ u O) (i : RIdx n) :
    ContDiffOn ℝ ∞ (ellipticFlux a u i) O := by
  classical
  apply ContDiffOn.sum
  intro j _
  exact (Complex.ofRealCLM.contDiff.comp_contDiffOn (ha i j)).mul
    (elliptic_contDiffOn_directionalDerivative hO hu (realVec j))

theorem ellipticDivergence_contDiffOn {n : ℕ}
    {a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ}
    {u : ComplexVector n → ℂ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) O)
    (hu : ContDiffOn ℝ ∞ u O) : ContDiffOn ℝ ∞ (ellipticDivergence a u) O := by
  classical
  apply ContDiffOn.sum
  intro i _
  exact elliptic_contDiffOn_directionalDerivative hO
    (ellipticFlux_contDiffOn hO ha hu i) (realVec i)

theorem ellipticDivergence_test_identity {n : ℕ}
    {a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ}
    {u φ : ComplexVector n → ℂ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) O)
    (hu : ContDiffOn ℝ ∞ u O) (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ) (hs : tsupport φ ⊆ O) :
    (∫ x, φ x * ellipticDivergence a u x ∂lebesgueC n) =
      -∑ i, ∫ x, fderiv ℝ φ x (realVec i) * ellipticFlux a u i x ∂lebesgueC n := by
  classical
  have hInt (i : RIdx n) : Integrable (fun x =>
      φ x * fderiv ℝ (ellipticFlux a u i) x (realVec i)) (lebesgueC n) := by
    rw [lebesgueC_eq_volume]
    exact elliptic_local_test_product_integrable hO hφ hcφ hs
      (elliptic_contDiffOn_directionalDerivative hO
        (ellipticFlux_contDiffOn hO ha hu i) (realVec i))
  change (∫ x, φ x * ∑ i, fderiv ℝ (ellipticFlux a u i) x (realVec i)
    ∂lebesgueC n) = _
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hInt i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact elliptic_local_test_integration_by_parts hO hφ hcφ hs
    (ellipticFlux_contDiffOn hO ha hu i) (realVec i)

end Yau.LeafProofs

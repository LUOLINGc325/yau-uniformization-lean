import Yau.LeafProofs.L10InteriorHessian
import Yau.LeafProofs.L10InteriorTest
import Yau.LeafProofs.L10InteriorHessianDensity

/-! The actual second-derivative residual has integral zero, without differentiating `Lu`. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff Topology ComplexConjugate

namespace Yau.LeafProofs

def ellipticHessianField {n : ℕ} (u : ComplexVector n → ℂ)
    (x : ComplexVector n) (k i : RIdx n) : ℂ :=
  fderiv ℝ (fun y => fderiv ℝ u y (realVec k)) x (realVec i)

def ellipticHessianResidual {n : ℕ}
    (a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    (b : ComplexVector n → RIdx n → ℝ) (η : ComplexVector n → ℝ)
    (u : ComplexVector n → ℂ) (x : ComplexVector n) : ℝ :=
  ellipticHessianFiniteResidual (fun i j => a x i j)
    (fun k i j => fderiv ℝ (fun y => a y i j) x (realVec k))
    (ellipticAdjustedDrift a b x) (fun i => fderiv ℝ η x (realVec i))
    (fun i => (fderiv ℝ u x (realVec i)).re) (fun k i => (ellipticHessianField u x k i).re)
    (η x) (LeafCandidates.ellipticOp a b u x).re +
  ellipticHessianFiniteResidual (fun i j => a x i j)
    (fun k i j => fderiv ℝ (fun y => a y i j) x (realVec k))
    (ellipticAdjustedDrift a b x) (fun i => fderiv ℝ η x (realVec i))
    (fun i => (fderiv ℝ u x (realVec i)).im) (fun k i => (ellipticHessianField u x k i).im)
    (η x) (LeafCandidates.ellipticOp a b u x).im

theorem ellipticFlux_fderiv_eq_hessian {n : ℕ}
    {a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ} {u : ComplexVector n → ℂ}
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) O)
    (hu : ContDiffOn ℝ ∞ u O) {x : ComplexVector n} (hx : x ∈ O) (k i : RIdx n) :
    fderiv ℝ (ellipticFlux a u i) x (realVec k) =
      (∑ j, (a x i j : ℂ) * ellipticHessianField u x k j) +
        ∑ j, (fderiv ℝ (fun y => a y i j) x (realVec k) : ℂ) *
          fderiv ℝ u x (realVec j) := by
  rw [ellipticFlux_fderiv_expand hO ha hu hx i k]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [elliptic_directional_derivatives_commute
    ((hu.contDiffAt (hO.mem_nhds hx)).of_le (by simp)) (realVec j) (realVec k)]
  rfl

theorem ellipticHessianResidual_eq {n : ℕ}
    {a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ}
    {b : ComplexVector n → RIdx n → ℝ} {η : ComplexVector n → ℝ}
    {u : ComplexVector n → ℂ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) O)
    (hu : ContDiffOn ℝ ∞ u O) (hη : ContDiff ℝ ∞ η)
    (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ O) (x : ComplexVector n) :
    ellipticHessianResidual a b η u x =
      ((∑ k, ∑ i, fderiv ℝ (ellipticEnergyTest η (fun y => fderiv ℝ u y (realVec k))) x
          (realVec i) * fderiv ℝ (ellipticFlux a u i) x (realVec k)) -
        ∑ k, fderiv ℝ (ellipticEnergyTest η (fun y => fderiv ℝ u y (realVec k))) x
          (realVec k) * ellipticDivergence a u x).re := by
  have hGrad (k : RIdx n) := elliptic_contDiffOn_directionalDerivative hO hu (realVec k)
  have hD (k i : RIdx n) :
      fderiv ℝ (ellipticEnergyTest η (fun y => fderiv ℝ u y (realVec k))) x (realVec i) =
      (η x)^2 • conj (ellipticHessianField u x k i) +
        (2 * η x * fderiv ℝ η x (realVec i)) • conj (fderiv ℝ u x (realVec k)) :=
    ellipticEnergyTest_fderiv_global hO hη hcη hsη (hGrad k) x (realVec i)
  by_cases hx : x ∈ O
  · unfold ellipticHessianResidual
    rw [ellipticHessianFiniteResidual_complex_test,
      ellipticOp_eq_divergence_add_drift_on hO ha hu hx, add_sub_cancel_right]
    simp_rw [← hD, ← ellipticFlux_fderiv_eq_hessian hO ha hu hx]
  · have hz : η x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hsη h))
    simp only [hD, hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, zero_mul, zero_smul, add_zero, Finset.sum_const_zero, sub_self, Complex.zero_re]
    unfold ellipticHessianResidual ellipticHessianFiniteResidual
    simp [hz]

theorem ellipticHessianResidual_integrable_zero {n : ℕ}
    {a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ}
    {b : ComplexVector n → RIdx n → ℝ} {η : ComplexVector n → ℝ}
    {u : ComplexVector n → ℂ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) O)
    (hu : ContDiffOn ℝ ∞ u O) (hη : ContDiff ℝ ∞ η)
    (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ O) :
    Integrable (ellipticHessianResidual a b η u) (lebesgueC n) ∧
      (∫ x, ellipticHessianResidual a b η u x ∂lebesgueC n) = 0 := by
  classical
  let φ (k : RIdx n) := ellipticEnergyTest η (fun y => fderiv ℝ u y (realVec k))
  have hφ (k : RIdx n) := ellipticEnergyTest_regular hO hη hcη hsη
    (elliptic_contDiffOn_directionalDerivative hO hu (realVec k))
  have hDφ (k i : RIdx n) : ContDiff ℝ ∞ (fun x => fderiv ℝ (φ k) x (realVec i)) :=
    ((hφ k).1.fderiv_right (by simp)).clm_apply contDiff_const
  have hProdInt (k i : RIdx n) : Integrable (fun x => fderiv ℝ (φ k) x (realVec i) *
      fderiv ℝ (ellipticFlux a u i) x (realVec k)) (lebesgueC n) := by
    rw [lebesgueC_eq_volume]
    exact elliptic_local_test_product_integrable hO (hDφ k i)
      ((hφ k).2.1.fderiv_apply ℝ (realVec i))
      ((tsupport_fderiv_apply_subset ℝ (realVec i)).trans (hφ k).2.2)
      (elliptic_contDiffOn_directionalDerivative hO (ellipticFlux_contDiffOn hO ha hu i) (realVec k))
  have hSourceInt (k : RIdx n) : Integrable (fun x => fderiv ℝ (φ k) x (realVec k) *
      ellipticDivergence a u x) (lebesgueC n) := by
    rw [lebesgueC_eq_volume]
    exact elliptic_local_test_product_integrable hO (hDφ k k)
      ((hφ k).2.1.fderiv_apply ℝ (realVec k))
      ((tsupport_fderiv_apply_subset ℝ (realVec k)).trans (hφ k).2.2)
      (ellipticDivergence_contDiffOn hO ha hu)
  have hSumInt := integrable_finsetSum Finset.univ (fun k _ =>
    integrable_finsetSum Finset.univ (fun i _ => hProdInt k i))
  have hSourceSumInt := integrable_finsetSum Finset.univ (fun k _ => hSourceInt k)
  have hInt : Integrable (fun x => (∑ k, ∑ i, fderiv ℝ (φ k) x (realVec i) *
      fderiv ℝ (ellipticFlux a u i) x (realVec k)) -
      ∑ k, fderiv ℝ (φ k) x (realVec k) * ellipticDivergence a u x) (lebesgueC n) :=
    hSumInt.sub hSourceSumInt
  have heq : ellipticHessianResidual a b η u = fun x =>
      ((∑ k, ∑ i, fderiv ℝ (φ k) x (realVec i) * fderiv ℝ (ellipticFlux a u i) x (realVec k)) -
        ∑ k, fderiv ℝ (φ k) x (realVec k) * ellipticDivergence a u x).re := by
    funext x
    exact ellipticHessianResidual_eq hO ha hu hη hcη hsη x
  rw [heq]
  refine ⟨Complex.reCLM.integrable_comp hInt, ?_⟩
  calc
    _ = (∫ x, (∑ k, ∑ i, fderiv ℝ (φ k) x (realVec i) *
        fderiv ℝ (ellipticFlux a u i) x (realVec k)) -
        ∑ k, fderiv ℝ (φ k) x (realVec k) * ellipticDivergence a u x ∂lebesgueC n).re := by
      simpa only [Complex.reCLM_apply] using Complex.reCLM.integral_comp_comm hInt
    _ = 0 := by
      rw [integral_sub hSumInt hSourceSumInt,
        integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun i _ => hProdInt k i)),
        integral_finsetSum _ (fun k _ => hSourceInt k)]
      have hsum : (∑ k, ∫ x, ∑ i, fderiv ℝ (φ k) x (realVec i) *
          fderiv ℝ (ellipticFlux a u i) x (realVec k) ∂lebesgueC n) =
          ∑ k, ∫ x, fderiv ℝ (φ k) x (realVec k) * ellipticDivergence a u x ∂lebesgueC n := by
        apply Finset.sum_congr rfl
        intro k _
        rw [integral_finsetSum _ (fun i _ => hProdInt k i)]
        exact (ellipticDivergence_differentiated_test_identity hO ha hu
          (hφ k).1 (hφ k).2.1 (hφ k).2.2 k).symm
      rw [hsum, sub_self]
      rfl

end Yau.LeafProofs

import Yau.LeafProofs.L10InteriorEnergyDensity

/-! The energy residual has integral zero for the original smooth operator. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff Topology ComplexConjugate

namespace Yau.LeafProofs

def ellipticCaccioppoliResidual {n : ℕ}
    (a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    (b : ComplexVector n → RIdx n → ℝ) (η : ComplexVector n → ℝ)
    (u : ComplexVector n → ℂ) (x : ComplexVector n) : ℝ :=
  ellipticFiniteResidual (fun i j => a x i j) (ellipticAdjustedDrift a b x)
    (fun i => (fderiv ℝ u x (realVec i)).re)
    (fun i => fderiv ℝ η x (realVec i)) (η x) (u x).re (LeafCandidates.ellipticOp a b u x).re +
  ellipticFiniteResidual (fun i j => a x i j) (ellipticAdjustedDrift a b x)
    (fun i => (fderiv ℝ u x (realVec i)).im)
    (fun i => fderiv ℝ η x (realVec i)) (η x) (u x).im (LeafCandidates.ellipticOp a b u x).im

theorem ellipticCaccioppoliResidual_eq {n : ℕ}
    {a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ}
    {b : ComplexVector n → RIdx n → ℝ} {η : ComplexVector n → ℝ}
    {u : ComplexVector n → ℂ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) O)
    (hu : ContDiffOn ℝ ∞ u O) (hη : ContDiff ℝ ∞ η)
    (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ O) (x : ComplexVector n) :
    ellipticCaccioppoliResidual a b η u x =
      ((∑ i, fderiv ℝ (ellipticEnergyTest η u) x (realVec i) * ellipticFlux a u i x) +
        ellipticEnergyTest η u x * ellipticDivergence a u x).re := by
  unfold ellipticCaccioppoliResidual
  rw [ellipticFiniteResidual_complex_test]
  simp_rw [← ellipticEnergyTest_fderiv_global hO hη hcη hsη hu]
  change ((∑ i, fderiv ℝ (ellipticEnergyTest η u) x (realVec i) * ellipticFlux a u i x) +
    ellipticEnergyTest η u x *
      (LeafCandidates.ellipticOp a b u x -
        ∑ i, (ellipticAdjustedDrift a b x i : ℂ) * fderiv ℝ u x (realVec i))).re = _
  by_cases hx : x ∈ O
  · rw [ellipticOp_eq_divergence_add_drift_on hO ha hu hx, add_sub_cancel_right]
  · have hz : η x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hsη h))
    simp only [ellipticEnergyTest, hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_smul, zero_mul, add_zero]

theorem ellipticCaccioppoliResidual_integrable_zero {n : ℕ}
    {a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ}
    {b : ComplexVector n → RIdx n → ℝ} {η : ComplexVector n → ℝ}
    {u : ComplexVector n → ℂ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) O)
    (hu : ContDiffOn ℝ ∞ u O) (hη : ContDiff ℝ ∞ η)
    (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ O) :
    Integrable (ellipticCaccioppoliResidual a b η u) (lebesgueC n) ∧
      (∫ x, ellipticCaccioppoliResidual a b η u x ∂lebesgueC n) = 0 := by
  classical
  let φ := ellipticEnergyTest η u
  obtain ⟨hφ, hcφ, hsφ⟩ := ellipticEnergyTest_regular hO hη hcη hsη hu
  have hDφ (e : ComplexVector n) : ContDiff ℝ ∞ (fun x => fderiv ℝ φ x e) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have hFluxInt (i : RIdx n) : Integrable (fun x =>
      fderiv ℝ φ x (realVec i) * ellipticFlux a u i x) (lebesgueC n) := by
    rw [lebesgueC_eq_volume]
    exact elliptic_local_test_product_integrable hO (hDφ (realVec i))
      (hcφ.fderiv_apply ℝ (realVec i))
      ((tsupport_fderiv_apply_subset ℝ (realVec i)).trans hsφ)
      (ellipticFlux_contDiffOn hO ha hu i)
  have hDivInt : Integrable (fun x => φ x * ellipticDivergence a u x) (lebesgueC n) := by
    rw [lebesgueC_eq_volume]
    exact elliptic_local_test_product_integrable hO hφ hcφ hsφ
      (ellipticDivergence_contDiffOn hO ha hu)
  have hSumInt := integrable_finsetSum Finset.univ (fun i _ => hFluxInt i)
  have hInt : Integrable (fun x => (∑ i,
      fderiv ℝ φ x (realVec i) * ellipticFlux a u i x) +
      φ x * ellipticDivergence a u x) (lebesgueC n) := hSumInt.add hDivInt
  have heq : ellipticCaccioppoliResidual a b η u = fun x =>
      ((∑ i, fderiv ℝ φ x (realVec i) * ellipticFlux a u i x) +
        φ x * ellipticDivergence a u x).re := by
    funext x
    exact ellipticCaccioppoliResidual_eq hO ha hu hη hcη hsη x
  rw [heq]
  refine ⟨Complex.reCLM.integrable_comp hInt, ?_⟩
  calc
    _ = (∫ x, (∑ i, fderiv ℝ φ x (realVec i) * ellipticFlux a u i x) +
        φ x * ellipticDivergence a u x ∂lebesgueC n).re := by
      simpa only [Complex.reCLM_apply] using Complex.reCLM.integral_comp_comm hInt
    _ = 0 := by
      rw [integral_add hSumInt hDivInt, integral_finsetSum _ (fun i _ => hFluxInt i),
        ellipticDivergence_test_identity hO ha hu hφ hcφ hsφ, add_neg_cancel]
      rfl

end Yau.LeafProofs

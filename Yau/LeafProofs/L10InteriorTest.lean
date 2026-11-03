import Yau.LeafProofs.L10InteriorIntegration

/-! The localized conjugate test used in the real-part energy estimate. -/

noncomputable section
open MeasureTheory
open scoped ContDiff Topology ComplexConjugate

namespace Yau.LeafProofs

def ellipticEnergyTest {n : ℕ} (η : ComplexVector n → ℝ)
    (u : ComplexVector n → ℂ) (x : ComplexVector n) : ℂ :=
  (η x) ^ 2 • conj (u x)

theorem ellipticEnergyTest_regular {n : ℕ}
    {η : ComplexVector n → ℝ} {u : ComplexVector n → ℂ}
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hη : ContDiff ℝ ∞ η)
    (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ O) (hu : ContDiffOn ℝ ∞ u O) :
    ContDiff ℝ ∞ (ellipticEnergyTest η u) ∧ HasCompactSupport (ellipticEnergyTest η u) ∧
      tsupport (ellipticEnergyTest η u) ⊆ O := by
  have hs2 : tsupport (fun x => (η x)^2) ⊆ tsupport η := by
    simpa only [pow_two] using (tsupport_mul_subset_left (f := η) (g := η))
  have hc2 : HasCompactSupport (fun x => (η x)^2) := by
    have h : HasCompactSupport (fun x => η x * η x) := hcη.mul_right
    simpa only [pow_two] using h
  have hconj : ContDiffOn ℝ ∞ (fun x => conj (u x)) O :=
    Complex.conjCLE.contDiff.comp_contDiffOn hu
  refine ⟨contDiff_smul_of_tsupport_subset hO (hη.pow 2) (hs2.trans hsη) hconj,
    hc2.smul_right, ?_⟩
  exact (tsupport_smul_subset_left _ _).trans (hs2.trans hsη)

theorem ellipticEnergyTest_fderiv {n : ℕ}
    {η : ComplexVector n → ℝ} {u : ComplexVector n → ℂ}
    {x : ComplexVector n} (hη : DifferentiableAt ℝ η x) (hu : DifferentiableAt ℝ u x)
    (e : ComplexVector n) :
    fderiv ℝ (ellipticEnergyTest η u) x e =
      (η x)^2 • conj (fderiv ℝ u x e) +
        (2 * η x * fderiv ℝ η x e) • conj (u x) := by
  have hconj : HasFDerivAt (fun y => conj (u y)) (Complex.conjCLE.toContinuousLinearMap.comp
      (fderiv ℝ u x)) x := by
    exact Complex.conjCLE.hasFDerivAt.comp x hu.hasFDerivAt
  have hsq : HasFDerivAt (fun y => (η y)^2) ((2 * η x) • fderiv ℝ η x) x := by
    convert (hη.hasFDerivAt.mul hη.hasFDerivAt) using 1 <;>
      simp only [pow_two, two_mul, add_smul]
    rfl
  unfold ellipticEnergyTest
  rw [fderiv_fun_smul hsq.differentiableAt hconj.differentiableAt, hsq.fderiv, hconj.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  rfl

theorem ellipticEnergyTest_fderiv_global {n : ℕ}
    {η : ComplexVector n → ℝ} {u : ComplexVector n → ℂ}
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hη : ContDiff ℝ ∞ η)
    (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ O) (hu : ContDiffOn ℝ ∞ u O)
    (x e : ComplexVector n) :
    fderiv ℝ (ellipticEnergyTest η u) x e =
      (η x)^2 • conj (fderiv ℝ u x e) +
        (2 * η x * fderiv ℝ η x e) • conj (u x) := by
  by_cases hx : x ∈ O
  · exact ellipticEnergyTest_fderiv ((hη.differentiable (by simp)).differentiableAt)
      ((hu.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)) e
  · have hnot : x ∉ tsupport η := fun h => hx (hsη h)
    have hz : η x = 0 := image_eq_zero_of_notMem_tsupport hnot
    have htestnot : x ∉ tsupport (ellipticEnergyTest η u) :=
      fun h => hx ((ellipticEnergyTest_regular hO hη hcη hsη hu).2.2 h)
    rw [fderiv_of_notMem_tsupport ℝ htestnot, hz]
    simp

theorem ellipticEnergyTest_divergence_identity {n : ℕ}
    {a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ}
    {η : ComplexVector n → ℝ} {u : ComplexVector n → ℂ}
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) O)
    (hu : ContDiffOn ℝ ∞ u O) (hη : ContDiff ℝ ∞ η)
    (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ O) :
    (∫ x, ellipticEnergyTest η u x * ellipticDivergence a u x ∂lebesgueC n) +
      (∑ i, ∫ x,
        ((η x)^2 • conj (fderiv ℝ u x (realVec i)) +
          (2 * η x * fderiv ℝ η x (realVec i)) • conj (u x)) *
            ellipticFlux a u i x ∂lebesgueC n) = 0 := by
  obtain ⟨hφ, hcφ, hsφ⟩ := ellipticEnergyTest_regular hO hη hcη hsη hu
  rw [ellipticDivergence_test_identity hO ha hu hφ hcφ hsφ]
  simp only [ellipticEnergyTest_fderiv_global hO hη hcη hsη hu]
  exact neg_add_cancel _

end Yau.LeafProofs

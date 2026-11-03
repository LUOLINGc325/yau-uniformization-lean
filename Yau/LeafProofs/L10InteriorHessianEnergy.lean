import Yau.LeafProofs.L10InteriorHessianNorm

/-! The weighted H² estimate consumes the original forcing only in L². -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff Topology
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.LeafProofs

theorem elliptic_hessian_weighted {n : ℕ}
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    {a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ}
    {b : ComplexVector n → RIdx n → ℝ} {η : ComplexVector n → ℝ}
    {u : ComplexVector n → ℂ} {ell A B M : ℝ}
    (hell : 0 < ell) (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) O)
    (hu : ContDiffOn ℝ ∞ u O) (hη : ContDiff ℝ ∞ η)
    (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ O)
    (hηBound : ∀ x, |η x| ≤ 1)
    (hηDeriv : ∀ x i, |fderiv ℝ η x (realVec i)| ≤ M)
    (hEll : ∀ x ∈ O, ∀ v : RIdx n → ℝ,
      ell * ∑ i, (v i)^2 ≤ ∑ i, ∑ j, a x i j * v i * v j)
    (haBound : ∀ x ∈ O, ∀ i j, |a x i j| ≤ A)
    (hDaBound : ∀ x ∈ O, ∀ k i j, |fderiv ℝ (fun y => a y i j) x (realVec k)| ≤ A)
    (hcBound : ∀ x ∈ O, ∀ i, |ellipticAdjustedDrift a b x i| ≤ B)
    (hu1 : IntegrableOn (fun x => ‖iteratedFDeriv ℝ 1 u x‖^2) O (lebesgueC n))
    (hu2 : IntegrableOn (fun x => ‖iteratedFDeriv ℝ 2 u x‖^2) O (lebesgueC n))
    (hF : IntegrableOn (fun x => ‖LeafCandidates.ellipticOp a b u x‖^2) O (lebesgueC n)) :
    (∫ x in O, (η x)^2 * ellipticHessianEnergy u x ∂lebesgueC n) ≤
      (2 * ellipticHessianAbsorptionConstant (Fintype.card (RIdx n)) ell A B M / ell) *
        ((∫ x in O, ellipticGradientEnergy u x ∂lebesgueC n) +
          ∫ x in O, ‖LeafCandidates.ellipticOp a b u x‖^2 ∂lebesgueC n) := by
  classical
  let C := ellipticHessianAbsorptionConstant (Fintype.card (RIdx n)) ell A B M
  obtain ⟨hRes, hResZero⟩ := ellipticHessianResidual_integrable_zero hO ha hu hη hcη hsη
  have hResOnZero : (∫ x in O, ellipticHessianResidual a b η u x ∂lebesgueC n) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact hResZero
    · intro x hx
      have hz : η x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hsη h))
      unfold ellipticHessianResidual ellipticHessianFiniteResidual
      simp [hz]
  have hEnergy := ellipticHessianEnergy_weighted_integrableOn hO hu hη hηBound hu2
  have hGrad := ellipticGradientEnergy_integrableOn hO hu hu1
  have hCZ : IntegrableOn (fun x => C * (ellipticGradientEnergy u x +
      ‖LeafCandidates.ellipticOp a b u x‖^2)) O (lebesgueC n) := (hGrad.add hF).const_mul C
  have hRhs : IntegrableOn (fun x => ellipticHessianResidual a b η u x +
      C * (ellipticGradientEnergy u x + ‖LeafCandidates.ellipticOp a b u x‖^2)) O (lebesgueC n) :=
    hRes.restrict.add hCZ
  have hI : (ell / 2) * (∫ x in O, (η x)^2 * ellipticHessianEnergy u x ∂lebesgueC n) ≤
      C * ((∫ x in O, ellipticGradientEnergy u x ∂lebesgueC n) +
        ∫ x in O, ‖LeafCandidates.ellipticOp a b u x‖^2 ∂lebesgueC n) := by
    have hbound := integral_mono_ae (hEnergy.const_mul (ell / 2)) hRhs
      (show ∀ᵐ x ∂(lebesgueC n).restrict O,
        (ell / 2) * ((η x)^2 * ellipticHessianEnergy u x) ≤
          ellipticHessianResidual a b η u x +
            C * (ellipticGradientEnergy u x + ‖LeafCandidates.ellipticOp a b u x‖^2) by
        filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
        exact elliptic_hessian_complex_absorption (fun i j => a x i j)
          (fun k i j => fderiv ℝ (fun y => a y i j) x (realVec k))
          (ellipticAdjustedDrift a b x) (fun i => fderiv ℝ η x (realVec i))
          (fun i => fderiv ℝ u x (realVec i)) (ellipticHessianField u x)
          (LeafCandidates.ellipticOp a b u x) (η x) ell A B M hell hA hB hM
          (haBound x hx) (hDaBound x hx) (hcBound x hx) (hηDeriv x) (hηBound x) (hEll x hx))
    simpa only [integral_add hRes.restrict hCZ, integral_const_mul,
      hResOnZero, zero_add, integral_add hGrad hF] using hbound
  have hdiv := (le_div_iff₀ (show 0 < ell / 2 by positivity)).mpr
    (by simpa only [mul_comm (ell / 2)] using hI)
  convert hdiv using 1
  ring

end Yau.LeafProofs

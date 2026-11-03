import Yau.LeafProofs.L10InteriorResidual
import Yau.LeafProofs.L10InteriorCutoff

/-! A uniform Caccioppoli estimate in the original real coordinates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff Topology
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.LeafProofs

def ellipticGradientEnergy {n : ℕ} (u : ComplexVector n → ℂ) (x : ComplexVector n) : ℝ :=
  ∑ i, ‖fderiv ℝ u x (realVec i)‖^2

theorem ellipticGradientEnergy_integrableOn {n : ℕ}
    {u : ComplexVector n → ℂ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ u O)
    (hi : IntegrableOn (fun x => ‖iteratedFDeriv ℝ 1 u x‖^2) O (lebesgueC n)) :
    IntegrableOn (ellipticGradientEnergy u) O (lebesgueC n) := by
  classical
  apply integrable_finsetSum
  intro i _
  simpa only [IntegrableOn, ellipticWordDerivative, iteratedFDeriv_one_apply] using
    ellipticWordDerivative_sq_integrableOn hO hu hi (fun _ : Fin 1 => i)

theorem ellipticGradientEnergy_weighted_integrableOn {n : ℕ}
    {u : ComplexVector n → ℂ} {η : ComplexVector n → ℝ}
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hu : ContDiffOn ℝ ∞ u O)
    (hη : ContDiff ℝ ∞ η) (hηBound : ∀ x, |η x| ≤ 1)
    (hi : IntegrableOn (fun x => ‖iteratedFDeriv ℝ 1 u x‖^2) O (lebesgueC n)) :
    IntegrableOn (fun x => (η x)^2 * ellipticGradientEnergy u x) O (lebesgueC n) := by
  have hQ := ellipticGradientEnergy_integrableOn hO hu hi
  have hWeight : ∀ x, ‖(η x)^2‖ ≤ 1 := by
    intro x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h := hηBound x
    nlinarith [abs_nonneg (η x), sq_abs (η x)]
  simpa only [IntegrableOn, Pi.pow_apply, mul_comm] using hQ.mul_bdd
    ((hη.continuous.pow 2).aestronglyMeasurable.restrict)
    (Filter.Eventually.of_forall hWeight)

theorem elliptic_caccioppoli_weighted {n : ℕ}
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
    (hcBound : ∀ x ∈ O, ∀ i, |ellipticAdjustedDrift a b x i| ≤ B)
    (hu0 : IntegrableOn (fun x => ‖u x‖^2) O (lebesgueC n))
    (hu1 : IntegrableOn (fun x => ‖iteratedFDeriv ℝ 1 u x‖^2) O (lebesgueC n))
    (hF : IntegrableOn (fun x => ‖LeafCandidates.ellipticOp a b u x‖^2) O (lebesgueC n)) :
    (∫ x in O, (η x)^2 * ellipticGradientEnergy u x ∂lebesgueC n) ≤
      (2 * ellipticAbsorptionConstant (Fintype.card (RIdx n)) ell A B M / ell) *
        ((∫ x in O, ‖u x‖^2 ∂lebesgueC n) +
          ∫ x in O, ‖LeafCandidates.ellipticOp a b u x‖^2 ∂lebesgueC n) := by
  classical
  let C := ellipticAbsorptionConstant (Fintype.card (RIdx n)) ell A B M
  have hC : 0 < C := ellipticAbsorptionConstant_pos _ hell
  obtain ⟨hRes, hResZero⟩ := ellipticCaccioppoliResidual_integrable_zero hO ha hu hη hcη hsη
  have hResOnZero : (∫ x in O, ellipticCaccioppoliResidual a b η u x ∂lebesgueC n) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact hResZero
    · intro x hx
      rw [ellipticCaccioppoliResidual_eq hO ha hu hη hcη hsη]
      have hnot : x ∉ tsupport (ellipticEnergyTest η u) := fun h =>
        hx ((ellipticEnergyTest_regular hO hη hcη hsη hu).2.2 h)
      simp only [fderiv_of_notMem_tsupport ℝ hnot, zero_apply, zero_mul,
        Finset.sum_const_zero, image_eq_zero_of_notMem_tsupport hnot, zero_add, Complex.zero_re]
  have hEnergy := ellipticGradientEnergy_weighted_integrableOn hO hu hη hηBound hu1
  have hCZ : IntegrableOn (fun x => C * (‖u x‖^2 + ‖LeafCandidates.ellipticOp a b u x‖^2))
      O (lebesgueC n) := (hu0.add hF).const_mul C
  have hRhs : IntegrableOn (fun x => ellipticCaccioppoliResidual a b η u x +
      C * (‖u x‖^2 + ‖LeafCandidates.ellipticOp a b u x‖^2)) O (lebesgueC n) :=
    hRes.restrict.add hCZ
  have hI :
      (ell / 2) * (∫ x in O, (η x)^2 * ellipticGradientEnergy u x ∂lebesgueC n) ≤
        C * ((∫ x in O, ‖u x‖^2 ∂lebesgueC n) +
          ∫ x in O, ‖LeafCandidates.ellipticOp a b u x‖^2 ∂lebesgueC n) := by
    have hbound := integral_mono_ae (hEnergy.const_mul (ell / 2))
      hRhs (show ∀ᵐ x ∂(lebesgueC n).restrict O,
        (ell / 2) * ((η x)^2 * ellipticGradientEnergy u x) ≤
          ellipticCaccioppoliResidual a b η u x +
            C * (‖u x‖^2 + ‖LeafCandidates.ellipticOp a b u x‖^2) by
        filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
        exact elliptic_complex_finite_energy_absorption (fun i j => a x i j)
          (ellipticAdjustedDrift a b x) (fun i => fderiv ℝ η x (realVec i))
          (fun i => fderiv ℝ u x (realVec i)) (u x) (LeafCandidates.ellipticOp a b u x)
          (η x) ell A B M hell hA hB hM (haBound x hx) (hcBound x hx)
          (hηBound x) (hηDeriv x) (hEll x hx))
    simpa only [integral_add hRes.restrict hCZ, integral_const_mul,
      hResOnZero, zero_add, integral_add hu0 hF] using hbound
  have hdiv := (le_div_iff₀ (show 0 < ell / 2 by positivity)).mpr
    (by simpa only [mul_comm (ell / 2)] using hI)
  convert hdiv using 1
  ring

theorem elliptic_caccioppoli_constant (n s : ℕ) (hn : 0 < n)
    (r R ell A : ℝ) (hr : 0 < r) (hrR : r < R) (hell : 0 < ell) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
        (b : ComplexVector n → RIdx n → ℝ),
      (∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) (Metric.ball 0 R)) →
      (∀ z ∈ Metric.ball 0 R, ∀ v : RIdx n → ℝ,
        ell * ∑ i, (v i)^2 ≤ ∑ i, ∑ j, a z i j * v i * v j) →
      (∀ k ≤ s + 1, ∀ z ∈ Metric.ball 0 R, ∀ i j,
        ‖iteratedFDeriv ℝ k (fun w => a w i j) z‖ ≤ A ∧
        ‖iteratedFDeriv ℝ k (fun w => b w i) z‖ ≤ A) →
      ∀ u : ComplexVector n → ℂ, ContDiffOn ℝ ∞ u (Metric.ball 0 R) →
      (∀ k ≤ s + 2, IntegrableOn (fun z => ‖iteratedFDeriv ℝ k u z‖^2)
        (Metric.ball 0 R) (lebesgueC n)) →
      (∀ k ≤ s, IntegrableOn (fun z => ‖iteratedFDeriv ℝ k (LeafCandidates.ellipticOp a b u) z‖^2)
        (Metric.ball 0 R) (lebesgueC n)) →
      (∫ z in Metric.ball 0 r, ellipticGradientEnergy u z ∂lebesgueC n) ≤
        C * ((∫ z in Metric.ball 0 R, ‖u z‖^2 ∂lebesgueC n) +
          ∫ z in Metric.ball 0 R, ‖LeafCandidates.ellipticOp a b u z‖^2 ∂lebesgueC n) := by
  obtain ⟨η, M, hM, hη, hcη, hsη, hηBound, hηDeriv, hηNear⟩ :=
    exists_elliptic_cutoff n hr hrR
  let B : ℝ := (2 * n + 1) * A
  let C : ℝ := 2 * ellipticAbsorptionConstant (Fintype.card (RIdx n)) ell A B M / ell
  have hB : 0 < B := by dsimp only [B]; positivity
  have hC : 0 < C := by
    dsimp only [C]
    exact div_pos (mul_pos (by norm_num) (ellipticAbsorptionConstant_pos _ hell)) hell
  refine ⟨C, hC, ?_⟩
  intro a b ha hEll hbound u hu hi hF
  have hco (z : ComplexVector n) (hz : z ∈ Metric.ball 0 R) :=
    elliptic_original_coefficient_bounds hn hbound hz
  have hu0 : IntegrableOn (fun z => ‖u z‖^2) (Metric.ball 0 R) (lebesgueC n) := by
    simpa only [norm_iteratedFDeriv_zero] using hi 0 (by omega)
  have hu1 := hi 1 (by omega)
  have hF0 : IntegrableOn (fun z => ‖LeafCandidates.ellipticOp a b u z‖^2)
      (Metric.ball 0 R) (lebesgueC n) := by
    simpa only [norm_iteratedFDeriv_zero] using hF 0 (Nat.zero_le s)
  have hWeighted := elliptic_caccioppoli_weighted Metric.isOpen_ball hell hA.le hB.le hM.le
    ha hu hη hcη hsη hηBound hηDeriv hEll
    (fun z hz => (hco z hz).1) (fun z hz => (hco z hz).2.2.2) hu0 hu1 hF0
  calc
    _ = ∫ z in Metric.ball 0 r, (η z)^2 * ellipticGradientEnergy u z ∂lebesgueC n := by
      apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      change ellipticGradientEnergy u z = (η z)^2 * ellipticGradientEnergy u z
      rw [(hηNear z hz).eq_of_nhds]
      simp
    _ ≤ ∫ z in Metric.ball 0 R, (η z)^2 * ellipticGradientEnergy u z ∂lebesgueC n := by
      apply setIntegral_mono_set
        (ellipticGradientEnergy_weighted_integrableOn Metric.isOpen_ball hu hη hηBound hu1)
        (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _)
          (Finset.sum_nonneg fun i _ => sq_nonneg _))
      exact Filter.Eventually.of_forall fun z hz => Metric.ball_subset_ball hrR.le hz
    _ ≤ _ := hWeighted

end Yau.LeafProofs

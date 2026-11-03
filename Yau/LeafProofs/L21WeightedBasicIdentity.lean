import Yau.LeafProofs.L21CompactTests
import Yau.LeafProofs.L21BasicIdentity

/-! The weighted basic identity on the actual common compact core. -/

open MeasureTheory
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ} {O : Set (X n)}

def testPair (φ : X n → ℝ) (f g : CompactTest O) : ℝ :=
  (∫ x, star (f x) * g x * weightDensity φ x ∂Yau.lebesgueC n).re

theorem integrable_test_pair (hO : IsOpen O) {φ : X n → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ O) (f g : CompactTest O) :
    Integrable (fun x => star (f x) * g x * weightDensity φ x) (Yau.lebesgueC n) := by
  have hs : Continuous (fun x => star (f x)) :=
    (starL' ℝ : ℂ ≃L[ℝ] ℂ).continuous.comp f.property.1.continuous
  have hw : ContDiffOn ℝ ∞ (weightDensity φ) O :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (Real.contDiff_exp.comp_contDiffOn hφ.neg)
  simpa only [Pi.mul_apply, mul_comm, mul_left_comm, mul_assoc] using
    Yau.LeafProofs.L14Aux.integrable_compactTest_mul_complex hO
      g.property.1.continuous g.property.2.1 g.property.2.2 (hs.continuousOn.mul hw.continuousOn)

theorem testPair_add_right (hO : IsOpen O) {φ : X n → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ O) (f g h : CompactTest O) :
    testPair φ f (g + h) = testPair φ f g + testPair φ f h := by
  simp only [testPair, AddSubgroup.coe_add, Pi.add_apply, mul_add, add_mul]
  rw [integral_add (integrable_test_pair hO hφ f g) (integrable_test_pair hO hφ f h), Complex.add_re]

theorem testPair_add_left (hO : IsOpen O) {φ : X n → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ O) (f g h : CompactTest O) :
    testPair φ (f + g) h = testPair φ f h + testPair φ g h := by
  simp only [testPair, AddSubgroup.coe_add, Pi.add_apply, star_add, add_mul]
  rw [integral_add (integrable_test_pair hO hφ f h) (integrable_test_pair hO hφ g h), Complex.add_re]

def testPairAdditive (hO : IsOpen O) {φ : X n → ℝ} (hφ : ContDiffOn ℝ ∞ φ O) :
    CompactTest O →+ CompactTest O →+ ℝ where
  toFun f :=
    { toFun := testPair φ f
      map_zero' := by simp [testPair]
      map_add' := testPair_add_right hO hφ f }
  map_zero' := by ext g; simp [testPair]
  map_add' f g := by ext h; exact testPair_add_left hO hφ f g h

theorem testPair_symm (hO : IsOpen O) {φ : X n → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ O) (f g : CompactTest O) : testPair φ f g = testPair φ g f := by
  unfold testPair
  simp only [← RCLike.re_eq_complex_re]
  rw [← integral_re (integrable_test_pair hO hφ f g), ← integral_re (integrable_test_pair hO hφ g f)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [RCLike.re_eq_complex_re]
  change (star (f x) * g x * (Real.exp (-φ x) : ℂ)).re =
    (star (g x) * f x * (Real.exp (-φ x) : ℂ)).re
  simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

def weightedScalarEnergy (φ : X n → ℝ) (f : X n → ℂ) : ℝ :=
  ∫ x, ‖f x‖ ^ 2 * Real.exp (-φ x) ∂Yau.lebesgueC n

theorem testPair_self_eq_weightedScalarEnergy (hO : IsOpen O) {φ : X n → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ O) (f : CompactTest O) :
    testPair φ f f = weightedScalarEnergy φ f := by
  unfold testPair weightedScalarEnergy
  simp only [← RCLike.re_eq_complex_re]
  rw [← integral_re (integrable_test_pair hO hφ f f)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [RCLike.re_eq_complex_re]
  change (star (f x) * f x * (Real.exp (-φ x) : ℂ)).re = ‖f x‖ ^ 2 * Real.exp (-φ x)
  simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sq_norm, Complex.normSq_apply]
  ring

theorem testPair_adjoint (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    {φ : X n → ℝ} (hφ : ContDiffOn ℝ ∞ φ O) (i : Fin n) (u v : CompactTest O) :
    testPair φ u (testD hO hA i v) = testPair φ (testDs hO hA hφ i u) v := by
  have he := integral_weighted_dbarA_green hO hA hφ v.property.1 u.property.1.contDiffOn
    v.property.2.1 v.property.2.2 i
  apply congrArg Complex.re at he
  change testPair φ u (testD hO hA i v) = _
  rw [show testPair φ u (testD hO hA i v) =
      (∫ x, star (weightedDStarDiv A φ i u x) * v x * weightDensity φ x ∂Yau.lebesgueC n).re from he]
  unfold testPair
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hv : v x = 0
  · simp only [hv, mul_zero, zero_mul]
  · have hx : x ∈ O := v.property.2.2 (subset_tsupport _ hv)
    rw [weightedDStarDiv_eq A φ i u x
      (fun a => ((dbarRealCoefficient_smoothOn hA i a).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
      ((hφ.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
      (u.property.1.differentiable (by simp) x)]
    rfl

theorem weighted_basic_identity_on_compact_tests (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    {φ : X n → ℝ} (hφ : ContDiffOn ℝ ∞ φ O) (v : Fin n → CompactTest O) :
    testPair φ (∑ i, testDs hO hA hφ i (v i)) (∑ i, testDs hO hA hφ i (v i)) +
        (1 / 2 : ℝ) * ∑ i, ∑ j,
          testPair φ (testD hO hA i (v j) - testD hO hA j (v i))
            (testD hO hA i (v j) - testD hO hA j (v i)) =
      (∑ i, ∑ j, testPair φ (testD hO hA i (v j)) (testD hO hA i (v j))) +
        ∑ i, ∑ j, testPair φ (v i)
          (testD hO hA i (testDs hO hA hφ j (v j)) - testDs hO hA hφ j (testD hO hA i (v j))) := by
  exact additive_basic_identity n (testPairAdditive hO hφ) (testPair_symm hO hφ)
    (testD hO hA) (testDs hO hA hφ) (testPair_adjoint hO hA hφ) v

end Yau.LeafProofs.L21Aux

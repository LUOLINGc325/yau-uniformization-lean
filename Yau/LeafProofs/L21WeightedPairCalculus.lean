import Yau.LeafProofs.L21WeightedPairBounds

/-! Actual weighted integration by parts moves a coefficient times Dstar
without producing any additional derivative of the singular weight. -/

open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ} {O : Set (X n)}

theorem compactTest_ext_on {u v : CompactTest O} (h : ∀ x ∈ O, u x = v x) : u = v := by
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ O
  · exact h x hx
  · rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (u.property.2.2 hh)),
      image_eq_zero_of_notMem_tsupport (fun hh => hx (v.property.2.2 hh))]

theorem testPair_sum_right {ι : Type*} [Fintype ι] (hO : IsOpen O) {φ : X n → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ O) (u : CompactTest O) (v : ι → CompactTest O) :
    testPair φ u (∑ i, v i) = ∑ i, testPair φ u (v i) :=
  map_sum (testPairAdditive hO hφ u) v Finset.univ

theorem testPair_multiply_transfer (hO : IsOpen O) {φ : X n → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ O) {a : X n → ℂ} (ha : ContDiffOn ℝ ∞ a O)
    (u v : CompactTest O) :
    testPair φ u (multiplyLocalTest hO ha v) =
      testPair φ (multiplyLocalTest hO ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn ha) u) v := by
  unfold testPair
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  change star (u x) * (a x * v x) * weightDensity φ x =
    star (star (a x) * u x) * v x * weightDensity φ x
  simp only [star_mul, star_star]
  ring

theorem testPair_adjoint_reverse (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    {φ : X n → ℝ} (hφ : ContDiffOn ℝ ∞ φ O) (i : Fin n) (u v : CompactTest O) :
    testPair φ u (testDs hO hA hφ i v) = testPair φ (testD hO hA i u) v := by
  rw [testPair_symm hO hφ u, ← testPair_adjoint hO hA hφ, testPair_symm hO hφ v]

theorem testD_multiplyLocalTest (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    {a : X n → ℂ} (ha : ContDiffOn ℝ ∞ a O) (i : Fin n) (u : CompactTest O) :
    testD hO hA i (multiplyLocalTest hO ha u) =
      multiplyLocalTest hO ha (testD hO hA i u) +
        multiplyLocalTest hO (contDiffOn_dbarA hO hA i ha) u := by
  apply compactTest_ext_on
  intro x hx
  change dbarA A i (fun y => a y * u y) x = a x * dbarA A i u x + dbarA A i a x * u x
  rw [dbarA_mul A i ((ha.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
    (u.property.1.differentiable (by simp) x)]
  ring

theorem testPair_coefficient_Dstar (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    {φ : X n → ℝ} (hφ : ContDiffOn ℝ ∞ φ O)
    {a : X n → ℂ} (ha : ContDiffOn ℝ ∞ a O) (i : Fin n) (u v : CompactTest O) :
    testPair φ u (multiplyLocalTest hO ha (testDs hO hA hφ i v)) =
      testPair φ v (multiplyLocalTest hO ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn ha)
        (testD hO hA i u)) +
      testPair φ u (multiplyLocalTest hO
        ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn
          (contDiffOn_dbarA hO hA i ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn ha))) v) := by
  let hs := (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn ha
  rw [testPair_multiply_transfer hO hφ ha,
    testPair_adjoint_reverse hO hA hφ, testD_multiplyLocalTest hO hA hs,
    testPair_add_left hO hφ]
  congr 1
  · exact testPair_symm hO hφ _ _
  · symm
    have hh := testPair_multiply_transfer hO hφ
      ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn (contDiffOn_dbarA hO hA i hs)) u v
    have he : multiplyLocalTest hO
        ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn
          ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn (contDiffOn_dbarA hO hA i hs))) u =
        multiplyLocalTest hO (contDiffOn_dbarA hO hA i hs) u := by
      apply Subtype.ext
      funext x
      change star (star (dbarA A i (fun y => star (a y)) x)) * u x = _
      rw [star_star]
      rfl
    rw [he] at hh
    exact hh

end Yau.LeafProofs.L21Aux

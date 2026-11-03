import Yau.LeafProofs.L21WeightedPairCalculus

/-! The actual weighted commutator identity on the literal common compact
core, followed by the coefficient integration by parts. -/

open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ} {O : Set (X n)}

theorem contDiffOn_correctedLevi (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    {φ : X n → ℝ} (hφ : ContDiffOn ℝ ∞ φ O)
    {d : Fin n → Fin n → Fin n → X n → ℂ}
    (hd : ∀ i j k, ContDiffOn ℝ ∞ (d i j k) O) (i j : Fin n) :
    ContDiffOn ℝ ∞ (correctedLevi A φ d i j) O :=
  (contDiffOn_dbarA hO hA i (contDiffOn_conjugateD hO hA j
    (Complex.ofRealCLM.contDiff.comp_contDiffOn hφ))).sub
    (ContDiffOn.sum fun k _ => (hd i j k).mul (contDiffOn_conjugateD hO hA k
      (Complex.ofRealCLM.contDiff.comp_contDiffOn hφ)))

theorem contDiffOn_weightedCommutatorRemainder (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    {d : Fin n → Fin n → Fin n → X n → ℂ}
    (hd : ∀ i j k, ContDiffOn ℝ ∞ (d i j k) O) (i j : Fin n) :
    ContDiffOn ℝ ∞ (weightedCommutatorRemainder A d i j) O :=
  (ContDiffOn.sum fun k _ => (hd i j k).mul (contDiffOn_conjugateDivergence hO hA k)).sub
    (contDiffOn_dbarA hO hA i (contDiffOn_conjugateDivergence hO hA j))

theorem compactTest_sum_apply {ι : Type*} [Fintype ι]
    (f : ι → CompactTest O) (x : X n) : (∑ i, f i) x = ∑ i, f i x := by
  let e : CompactTest O →+ ℂ :=
    { toFun := fun u => u x
      map_zero' := rfl
      map_add' := fun u v => rfl }
  exact map_sum e f Finset.univ

theorem compact_weighted_commutator (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    {φ : X n → ℝ} (hφ : ContDiffOn ℝ ∞ φ O)
    (c d : Fin n → Fin n → Fin n → X n → ℂ)
    (hc : ∀ i j k, ContDiffOn ℝ ∞ (c i j k) O)
    (hd : ∀ i j k, ContDiffOn ℝ ∞ (d i j k) O)
    (hbr : ∀ f : X n → ℂ, ContDiffOn ℝ ∞ f O → ∀ x ∈ O, ∀ i j,
      dbarA A i (conjugateD A j f) x - conjugateD A j (dbarA A i f) x =
        ∑ k, (c i j k x * dbarA A k f x + d i j k x * conjugateD A k f x))
    (i j : Fin n) (v : CompactTest O) :
    testD hO hA i (testDs hO hA hφ j v) - testDs hO hA hφ j (testD hO hA i v) =
      (∑ k, (multiplyLocalTest hO (hc i j k).neg (testD hO hA k v) +
        multiplyLocalTest hO (hd i j k) (testDs hO hA hφ k v))) +
      multiplyLocalTest hO (contDiffOn_correctedLevi hO hA hφ hd i j) v +
      multiplyLocalTest hO (contDiffOn_weightedCommutatorRemainder hO hA hd i j) v := by
  apply compactTest_ext_on
  intro x hx
  change dbarA A i (weightedDStar A φ j v) x - weightedDStar A φ j (dbarA A i v) x =
    ((∑ k, (multiplyLocalTest hO (hc i j k).neg (testD hO hA k v) +
      multiplyLocalTest hO (hd i j k) (testDs hO hA hφ k v))) : CompactTest O) x +
    correctedLevi A φ d i j x * v x + weightedCommutatorRemainder A d i j x * v x
  rw [compactTest_sum_apply]
  exact weighted_commutator_expansion hO hA hφ c d v.property.1.contDiffOn hx i j
    (hbr v v.property.1.contDiffOn x hx i j)

theorem compact_commutator_pair_expansion (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    {φ : X n → ℝ} (hφ : ContDiffOn ℝ ∞ φ O)
    (c d : Fin n → Fin n → Fin n → X n → ℂ)
    (hc : ∀ i j k, ContDiffOn ℝ ∞ (c i j k) O)
    (hd : ∀ i j k, ContDiffOn ℝ ∞ (d i j k) O)
    (hbr : ∀ f : X n → ℂ, ContDiffOn ℝ ∞ f O → ∀ x ∈ O, ∀ i j,
      dbarA A i (conjugateD A j f) x - conjugateD A j (dbarA A i f) x =
        ∑ k, (c i j k x * dbarA A k f x + d i j k x * conjugateD A k f x))
    (i j : Fin n) (u v : CompactTest O) :
    testPair φ u (testD hO hA i (testDs hO hA hφ j v) - testDs hO hA hφ j (testD hO hA i v)) =
      (∑ k, (testPair φ u (multiplyLocalTest hO (hc i j k).neg (testD hO hA k v)) +
        testPair φ v (multiplyLocalTest hO
          ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn (hd i j k)) (testD hO hA k u)) +
        testPair φ u (multiplyLocalTest hO
          ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn (contDiffOn_dbarA hO hA k
            ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn (hd i j k)))) v))) +
      testPair φ u (multiplyLocalTest hO (contDiffOn_correctedLevi hO hA hφ hd i j) v) +
      testPair φ u (multiplyLocalTest hO (contDiffOn_weightedCommutatorRemainder hO hA hd i j) v) := by
  rw [compact_weighted_commutator hO hA hφ c d hc hd hbr,
    testPair_add_right hO hφ, testPair_add_right hO hφ, testPair_sum_right hO hφ]
  congr 2
  apply Finset.sum_congr rfl
  intro k _
  rw [testPair_add_right hO hφ, testPair_coefficient_Dstar hO hA hφ]
  ring

end Yau.LeafProofs.L21Aux

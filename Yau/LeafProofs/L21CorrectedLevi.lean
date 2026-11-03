import Yau.LeafProofs.L21MixedFrameRows
import Yau.LeafProofs.L21WeightedBasicIdentity

/-! The corrected Levi matrix and the actual weighted commutator. The
bracket correction is retained explicitly, including every weight derivative. -/

open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def correctedLevi (A : X n → Matrix (Fin n) (Fin n) ℂ) (φ : X n → ℝ)
    (d : Fin n → Fin n → Fin n → X n → ℂ) (i j : Fin n) (x : X n) : ℂ :=
  dbarA A i (conjugateD A j (fun y => (φ y : ℂ))) x -
    ∑ k, d i j k x * conjugateD A k (fun y => (φ y : ℂ)) x

def weightedCommutatorRemainder (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → Fin n → Fin n → X n → ℂ) (i j : Fin n) (x : X n) : ℂ :=
  (∑ k, d i j k x * conjugateDivergence A k x) - dbarA A i (conjugateDivergence A j) x

theorem contDiffOn_conjugateD {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (i : Fin n) {f : X n → ℂ} (hf : ContDiffOn ℝ ∞ f O) :
    ContDiffOn ℝ ∞ (conjugateD A i f) O :=
  contDiffOn_real_row_sum hO Yau.realVec _
    (fun a => (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn (dbarRealCoefficient_smoothOn hA i a)) hf

theorem contDiffOn_conjugateDivergence {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O) (i : Fin n) :
    ContDiffOn ℝ ∞ (conjugateDivergence A i) O := by
  apply ContDiffOn.sum
  intro a _
  exact (((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn
    (dbarRealCoefficient_smoothOn hA i a)).fderiv_of_isOpen hO
      (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).clm_apply contDiffOn_const

theorem dbarA_neg (A : X n → Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (f : X n → ℂ) (x : X n) : dbarA A i (-f) x = -dbarA A i f x := by
  simp only [dbarA_eq_real_rows, fderiv_neg, _root_.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem dbarA_sub (A : X n → Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    {f g : X n → ℂ} {x : X n} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    dbarA A i (f - g) x = dbarA A i f x - dbarA A i g x := by
  simp only [dbarA_eq_real_rows, fderiv_sub hf hg, _root_.sub_apply,
    mul_sub, Finset.sum_sub_distrib]

theorem weighted_commutator_expansion {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    {φ : X n → ℝ} (hφ : ContDiffOn ℝ ∞ φ O)
    (c d : Fin n → Fin n → Fin n → X n → ℂ)
    {f : X n → ℂ} (hf : ContDiffOn ℝ ∞ f O) {x : X n} (hx : x ∈ O) (i j : Fin n)
    (hbr : dbarA A i (conjugateD A j f) x - conjugateD A j (dbarA A i f) x =
      ∑ k, (c i j k x * dbarA A k f x + d i j k x * conjugateD A k f x)) :
    dbarA A i (weightedDStar A φ j f) x - weightedDStar A φ j (dbarA A i f) x =
      (∑ k, (-c i j k x * dbarA A k f x + d i j k x * weightedDStar A φ k f x)) +
        correctedLevi A φ d i j x * f x + weightedCommutatorRemainder A d i j x * f x := by
  let Q (k : Fin n) : X n → ℂ := conjugateD A k (fun y => (φ y : ℂ))
  let B : X n → ℂ := Q j - conjugateDivergence A j
  have hQ (k : Fin n) : ContDiffOn ℝ ∞ (Q k) O :=
    contDiffOn_conjugateD hO hA k (Complex.ofRealCLM.contDiff.comp_contDiffOn hφ)
  have hdiv := contDiffOn_conjugateDivergence hO hA j
  have hB : DifferentiableAt ℝ B x :=
    (((hQ j).sub hdiv).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hF := (hf.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hconj := ((contDiffOn_conjugateD hO hA j hf).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hD : dbarA A i (weightedDStar A φ j f) x =
      -dbarA A i (conjugateD A j f) x +
        (f x * dbarA A i B x + B x * dbarA A i f x) := by
    change dbarA A i ((-conjugateD A j f) + (fun y => B y * f y)) x = _
    rw [dbarA_add A i (f := -conjugateD A j f) (g := fun y => B y * f y)
      hconj.neg (hB.mul hF), dbarA_neg, dbarA_mul A i hB hF]
    ring
  have hDB : dbarA A i B x = dbarA A i (Q j) x - dbarA A i (conjugateDivergence A j) x :=
    dbarA_sub A i (((hQ j).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
      ((hdiv.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
  have hSum : (∑ k, (-c i j k x * dbarA A k f x + d i j k x * weightedDStar A φ k f x)) =
      -(∑ k, (c i j k x * dbarA A k f x + d i j k x * conjugateD A k f x)) +
        ((∑ k, d i j k x * Q k x) - (∑ k, d i j k x * conjugateDivergence A k x)) * f x := by
    calc
      _ = ∑ k, (-(c i j k x * dbarA A k f x + d i j k x * conjugateD A k f x) +
          (d i j k x * Q k x - d i j k x * conjugateDivergence A k x) * f x) := by
        apply Finset.sum_congr rfl
        intro k _
        dsimp only [weightedDStar, Q]
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, sub_mul,
          Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hD, hDB, hSum]
  dsimp only [weightedDStar, B, Pi.sub_apply, correctedLevi, weightedCommutatorRemainder, Q]
  linear_combination -hbr

end Yau.LeafProofs.L21Aux

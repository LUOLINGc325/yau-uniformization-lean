import Yau.LeafProofs.L21MixedFrameInverse
import Yau.LeafProofs.L21FirstOrderCalculus
import Mathlib.Analysis.Calculus.FDeriv.Star

open scoped ContDiff Topology
noncomputable section
set_option maxHeartbeats 2000000
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def mixedFrameDerivativeSize (A : X n → Matrix (Fin n) (Fin n) ℂ) (x : X n) : ℝ :=
  ∑ i, ∑ k, ‖fderiv ℝ (fun y => A y i k) x‖

def mixedFrameHolomorphicBracket (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (i j k : Fin n) (x : X n) : ℂ := -conjugateD A j (fun y => A y i k) x

def mixedFrameAntiholomorphicBracket (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (i j k : Fin n) (x : X n) : ℂ := dbarA A i (fun y => star (A y j k)) x

def mixedFrameBracketData (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) (x : X n) : MixedFrameVector n :=
  (fun k => mixedFrameAntiholomorphicBracket A i j k x,
    fun k => mixedFrameHolomorphicBracket A i j k x)

def mixedFrameCoefficientVector (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) (x : X n) : MixedFrameVector n :=
  (mixedFrameOperator (A x)).inverse (mixedFrameBracketData A i j x)

def mixedFrameC (A : X n → Matrix (Fin n) (Fin n) ℂ) (i j k : Fin n) (x : X n) : ℂ :=
  (mixedFrameCoefficientVector A i j x).1 k

def mixedFrameD (A : X n → Matrix (Fin n) (Fin n) ℂ) (i j k : Fin n) (x : X n) : ℂ :=
  (mixedFrameCoefficientVector A i j x).2 k

/-- Conjugation acts on the actual field coefficients, not on its input. -/
theorem mixedFrame_dbarA_star (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (i : Fin n) (f : X n → ℂ) (x : X n) :
    dbarA A i (fun y => star (f y)) x = star (conjugateD A i f x) := by
  rw [dbarA_eq_real_rows]
  have hs (v : X n) : fderiv ℝ (fun y => star (f y)) x v = star (fderiv ℝ f x v) :=
    congrArg (fun L : X n →L[ℝ] ℂ => L v) (fderiv_star (𝕜 := ℝ) (f := f) (x := x))
  simp only [conjugateD, star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro a _
  rw [hs]
  ring

theorem mixedFrame_conjugate_row (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (i : Fin n) (a : Yau.RIdx n) (x : X n) :
    star (dbarRealCoefficient A i a x) =
      (if a.1 = i then wirtRealCoefficient a.2 else 0)+star (A x i a.1)*wirtBarRealCoefficient a.2 := by
  rcases a with ⟨k,t⟩
  fin_cases t <;> by_cases hk : k = i <;>
    simp [dbarRealCoefficient,wirtRealCoefficient,wirtBarRealCoefficient,hk]

def mixedFrameConjugateSwap (w : MixedFrameVector n) : MixedFrameVector n :=
  (fun k => star (w.2 k),fun k => star (w.1 k))

theorem mixedFrameOperator_conjugate_swap (A : Matrix (Fin n) (Fin n) ℂ) (w : MixedFrameVector n) :
    mixedFrameOperator A (mixedFrameConjugateSwap w) = mixedFrameConjugateSwap (mixedFrameOperator A w) := by
  rw [mixedFrameOperator_apply,mixedFrameOperator_apply]
  ext k <;> simp [mixedFrameConjugateSwap,star_add,star_sum,star_mul,mul_comm]

theorem mixedFrameBracketData_skew (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) (x : X n) :
    mixedFrameBracketData A i j x = -mixedFrameConjugateSwap (mixedFrameBracketData A j i x) := by
  apply Prod.ext
  · funext k
    change dbarA A i (fun y => star (A y j k)) x = -star (-conjugateD A i (fun y => A y j k) x)
    rw [mixedFrame_dbarA_star]
    simp
  · funext k
    change -conjugateD A j (fun y => A y i k) x = -star (dbarA A j (fun y => star (A y i k)) x)
    rw [mixedFrame_dbarA_star]
    simp

/-- This is actual inverse reconstruction in the coefficient frame. -/
theorem mixedFrameCoefficientVector_equation {A : X n → Matrix (Fin n) (Fin n) ℂ}
    {x : X n} (hSmall : ∀ i k, ‖A x i k‖ ≤ mixedFrameEpsilon n) (i j : Fin n) :
    mixedFrameOperator (A x) (mixedFrameCoefficientVector A i j x) = mixedFrameBracketData A i j x :=
  (mixedFrameOperator_invertible hSmall).self_apply_inverse _

theorem mixedFrame_coefficients_conjugate {A : X n → Matrix (Fin n) (Fin n) ℂ}
    {x : X n} (hSmall : ∀ i k, ‖A x i k‖ ≤ mixedFrameEpsilon n) (i j k : Fin n) :
    star (mixedFrameD A j i k x) = -mixedFrameC A i j k x := by
  have hEq : mixedFrameCoefficientVector A i j x = -mixedFrameConjugateSwap (mixedFrameCoefficientVector A j i x) := by
    apply (mixedFrameOperator_invertible hSmall).injective
    rw [map_neg,mixedFrameOperator_conjugate_swap,mixedFrameCoefficientVector_equation hSmall,
      mixedFrameCoefficientVector_equation hSmall,mixedFrameBracketData_skew A i j x]
  have h := congrArg (fun w : MixedFrameVector n => w.1 k) hEq
  change mixedFrameC A i j k x = -star (mixedFrameD A j i k x) at h
  simpa only [neg_neg] using (congrArg Neg.neg h).symm

theorem mixedFrame_rowApply_contDiffAt {ι : Type*} [Fintype ι]
    (v : ι → X n) (p : ι → X n → ℂ) {f : X n → ℂ} {x : X n}
    (hp : ∀ a, ContDiffAt ℝ ∞ (p a) x) (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ ∞ (rowApply v p f) x := by
  unfold rowApply
  apply ContDiffAt.sum
  intro a _
  exact (hp a).mul ((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const)

theorem mixedFrameBracketData_smooth {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O) (i j : Fin n) :
    ContDiffOn ℝ ∞ (mixedFrameBracketData A i j) O := by
  intro x hx
  have hp (r : Fin n) (a : Yau.RIdx n) : ContDiffAt ℝ ∞ (dbarRealCoefficient A r a) x :=
    (dbarRealCoefficient_smoothOn hA r a).contDiffAt (hO.mem_nhds hx)
  have hq (r : Fin n) (a : Yau.RIdx n) : ContDiffAt ℝ ∞ (fun y => star (dbarRealCoefficient A r a y)) x :=
    (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffAt x (hp r a)
  have hEntry (r k : Fin n) : ContDiffAt ℝ ∞ (fun y => A y r k) x :=
    (hA r k).contDiffAt (hO.mem_nhds hx)
  have hH (k : Fin n) : ContDiffAt ℝ ∞ (mixedFrameHolomorphicBracket A i j k) x :=
    (mixedFrame_rowApply_contDiffAt Yau.realVec (fun a y => star (dbarRealCoefficient A j a y))
      (hq j) (hEntry i k)).neg
  have hK (k : Fin n) : ContDiffAt ℝ ∞ (mixedFrameAntiholomorphicBracket A i j k) x := by
    have hEq : mixedFrameAntiholomorphicBracket A i j k =
        rowApply Yau.realVec (dbarRealCoefficient A i) (fun y => star (A y j k)) := by
      funext y
      exact dbarA_eq_real_rows A i _ y
    rw [hEq]
    exact mixedFrame_rowApply_contDiffAt Yau.realVec (dbarRealCoefficient A i) (hp i)
      ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffAt x (hEntry j k))
  exact ((contDiffAt_pi.mpr hK).prodMk (contDiffAt_pi.mpr hH)).contDiffWithinAt

theorem mixedFrame_coefficients_smooth {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (hSmall : JetBound 0 (mixedFrameEpsilon n) A O) (i j k : Fin n) :
    ContDiffOn ℝ ∞ (mixedFrameC A i j k) O ∧ ContDiffOn ℝ ∞ (mixedFrameD A i j k) O := by
  have hW : ContDiffOn ℝ ∞ (mixedFrameCoefficientVector A i j) O :=
    (mixedFrameOperator_inverse_smooth hO hA hSmall).clm_apply (mixedFrameBracketData_smooth hO hA i j)
  constructor <;> intro x hx
  · exact (contDiffAt_pi.mp ((hW.contDiffAt (hO.mem_nhds hx)).fst) k).contDiffWithinAt
  · exact (contDiffAt_pi.mp ((hW.contDiffAt (hO.mem_nhds hx)).snd) k).contDiffWithinAt

theorem mixedFrame_rowApply_affine {ι : Type*} [Fintype ι]
    (v : ι → X n) (p : ι → X n → ℂ) {f : X n → ℂ} {x : X n}
    (hf : DifferentiableAt ℝ f x) (a b : ℂ) :
    rowApply v p (fun y => a + f y*b) x = b*rowApply v p f x := by
  unfold rowApply
  simp only [fderiv_fun_add (differentiableAt_const a) (hf.mul_const b),
    fderiv_const_apply, zero_add, fderiv_fun_mul hf (differentiableAt_const b),
    _root_.add_apply, _root_.smul_apply, _root_.zero_apply, mul_zero,
    zero_add, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

set_option backward.isDefEq.respectTransparency false in
theorem mixedFrame_row_combination (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (w : MixedFrameVector n) (a : Yau.RIdx n) (x : X n) :
    (∑ k, (w.1 k*dbarRealCoefficient A k a x+w.2 k*star (dbarRealCoefficient A k a x))) =
      (mixedFrameOperator (A x) w).1 a.1*wirtBarRealCoefficient a.2+
      (mixedFrameOperator (A x) w).2 a.1*wirtRealCoefficient a.2 := by
  classical
  calc
    _ = (∑ k, if a.1=k then w.1 k*wirtBarRealCoefficient a.2 else 0)+
        (∑ k, if a.1=k then w.2 k*wirtRealCoefficient a.2 else 0)+
        (∑ k, (w.1 k*A x k a.1)*wirtRealCoefficient a.2)+
        (∑ k, (w.2 k*star (A x k a.1))*wirtBarRealCoefficient a.2) := by
      rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [mixedFrame_conjugate_row]
      dsimp only [dbarRealCoefficient]
      split_ifs <;> ring
    _ = w.1 a.1*wirtBarRealCoefficient a.2+w.2 a.1*wirtRealCoefficient a.2+
        (∑ k, w.1 k*A x k a.1)*wirtRealCoefficient a.2+
        (∑ k, w.2 k*star (A x k a.1))*wirtBarRealCoefficient a.2 := by
      rw [Finset.sum_ite_eq,Finset.sum_ite_eq,← Finset.sum_mul,← Finset.sum_mul]
      simp only [Finset.mem_univ,ite_true]
    _ = _ := by rw [mixedFrameOperator_apply]; dsimp only; ring

theorem mixedFrame_bracket_row {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    {x : X n} (hx : x ∈ O) (i j : Fin n) (a : Yau.RIdx n) :
    rowApply Yau.realVec (dbarRealCoefficient A i)
        (fun y => star (dbarRealCoefficient A j a y)) x -
      rowApply Yau.realVec (fun b y => star (dbarRealCoefficient A j b y))
        (dbarRealCoefficient A i a) x =
      mixedFrameAntiholomorphicBracket A i j a.1 x*wirtBarRealCoefficient a.2+
      mixedFrameHolomorphicBracket A i j a.1 x*wirtRealCoefficient a.2 := by
  have hEntry (r k : Fin n) := ((hA r k).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hStar : (fun y => star (dbarRealCoefficient A j a y)) =
      (fun y => (if a.1=j then wirtRealCoefficient a.2 else 0)+star (A y j a.1)*wirtBarRealCoefficient a.2) :=
    funext (fun y => mixedFrame_conjugate_row A j a y)
  rw [hStar,mixedFrame_rowApply_affine _ _ (hEntry j a.1).star]
  change _ - rowApply Yau.realVec (fun b y => star (dbarRealCoefficient A j b y))
      (fun y => (if a.1=i then wirtBarRealCoefficient a.2 else 0)+A y i a.1*wirtRealCoefficient a.2) x = _
  rw [mixedFrame_rowApply_affine _ _ (hEntry i a.1)]
  simp only [mixedFrameAntiholomorphicBracket,mixedFrameHolomorphicBracket,
    dbarA_eq_real_rows,conjugateD,rowApply]
  ring

theorem mixedFrame_commutator {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    {x : X n} (hx : x ∈ O) (hSmall : ∀ r k, ‖A x r k‖ ≤ mixedFrameEpsilon n)
    {f : X n → ℂ} (hf : ContDiffOn ℝ ∞ f O) (i j : Fin n) :
    dbarA A i (conjugateD A j f) x - conjugateD A j (dbarA A i f) x =
      ∑ k, (mixedFrameC A i j k x*dbarA A k f x+
        mixedFrameD A i j k x*conjugateD A k f x) := by
  have hp (r : Fin n) (a : Yau.RIdx n) :=
    ((dbarRealCoefficient_smoothOn hA r a).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hq (a : Yau.RIdx n) := (hp j a).star
  have hfAt := hf.contDiffAt (hO.mem_nhds hx)
  have hEq (r : Fin n) : dbarA A r f = rowApply Yau.realVec (dbarRealCoefficient A r) f :=
    funext (dbarA_eq_real_rows A r f)
  rw [hEq i,dbarA_eq_real_rows]
  change rowApply Yau.realVec (dbarRealCoefficient A i)
      (rowApply Yau.realVec (fun a y => star (dbarRealCoefficient A j a y)) f) x -
    rowApply Yau.realVec (fun a y => star (dbarRealCoefficient A j a y))
      (rowApply Yau.realVec (dbarRealCoefficient A i) f) x = _
  rw [rowApply_commutator _ _ _ (hp i) hq hfAt]
  have hRow (a : Yau.RIdx n) :
      rowApply Yau.realVec (dbarRealCoefficient A i) (fun y => star (dbarRealCoefficient A j a y)) x-
        rowApply Yau.realVec (fun b y => star (dbarRealCoefficient A j b y)) (dbarRealCoefficient A i a) x =
      ∑ k, (mixedFrameC A i j k x*dbarRealCoefficient A k a x+
        mixedFrameD A i j k x*star (dbarRealCoefficient A k a x)) := by
    rw [mixedFrame_bracket_row hO hA hx]
    symm
    change (∑ k, ((mixedFrameCoefficientVector A i j x).1 k*dbarRealCoefficient A k a x+
      (mixedFrameCoefficientVector A i j x).2 k*star (dbarRealCoefficient A k a x))) = _
    rw [mixedFrame_row_combination,mixedFrameCoefficientVector_equation hSmall]
    rfl
  simp only [hRow,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [dbarA_eq_real_rows,conjugateD,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

end Yau.LeafProofs.L21Aux

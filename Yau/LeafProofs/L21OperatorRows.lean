import Yau.LeafProofs.L21Integrability

/-! Actual real-coordinate rows of `dbarA`, and the corresponding formal
transpose and weighted conjugate transpose. -/

open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def wirtRealCoefficient (t : Fin 2) : ℂ :=
  if t = 0 then 1 / 2 else -Complex.I / 2

def wirtBarRealCoefficient (t : Fin 2) : ℂ :=
  if t = 0 then 1 / 2 else Complex.I / 2

theorem wirt_eq_real_directions (f : X n → ℂ) (x : X n) (i : Fin n) :
    Yau.wirt f x (Yau.stdVec i) =
      wirtRealCoefficient 0 * fderiv ℝ f x (Yau.realVec (i, 0)) +
      wirtRealCoefficient 1 * fderiv ℝ f x (Yau.realVec (i, 1)) := by
  simp only [Yau.wirt, wirtRealCoefficient, Yau.realVec, Yau.stdVec, ite_true, one_smul]
  norm_num
  ring

theorem wirtBar_eq_real_directions (f : X n → ℂ) (x : X n) (i : Fin n) :
    Yau.wirtBar f x (Yau.stdVec i) =
      wirtBarRealCoefficient 0 * fderiv ℝ f x (Yau.realVec (i, 0)) +
      wirtBarRealCoefficient 1 * fderiv ℝ f x (Yau.realVec (i, 1)) := by
  simp only [Yau.wirtBar, wirtBarRealCoefficient, Yau.realVec, Yau.stdVec, ite_true, one_smul]
  norm_num
  ring

def dbarRealCoefficient (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (i : Fin n) (a : Yau.RIdx n) (x : X n) : ℂ :=
  (if a.1 = i then wirtBarRealCoefficient a.2 else 0) +
    A x i a.1 * wirtRealCoefficient a.2

theorem dbarA_eq_real_rows (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (i : Fin n) (f : X n → ℂ) (x : X n) :
    dbarA A i f x =
      ∑ a : Yau.RIdx n, dbarRealCoefficient A i a x * fderiv ℝ f x (Yau.realVec a) := by
  simp only [dbarA, wirtBar_eq_real_directions, wirt_eq_real_directions,
    dbarRealCoefficient, Fintype.sum_prod_type, Fin.sum_univ_two,
    add_mul, mul_add, Finset.sum_add_distrib, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_assoc]

def conjugateD (A : X n → Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (f : X n → ℂ) (x : X n) : ℂ :=
  ∑ a : Yau.RIdx n, star (dbarRealCoefficient A i a x) * fderiv ℝ f x (Yau.realVec a)

def conjugateDivergence (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (i : Fin n) (x : X n) : ℂ :=
  ∑ a : Yau.RIdx n, fderiv ℝ (fun y => star (dbarRealCoefficient A i a y)) x (Yau.realVec a)

def weightedDStar (A : X n → Matrix (Fin n) (Fin n) ℂ) (φ : X n → ℝ)
    (i : Fin n) (f : X n → ℂ) (x : X n) : ℂ :=
  -conjugateD A i f x +
    (conjugateD A i (fun y => (φ y : ℂ)) x - conjugateDivergence A i x) * f x

def transposeRow (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (i : Fin n) (ψ : X n → ℝ) (x : X n) : ℂ :=
  -(∑ a : Yau.RIdx n,
    (dbarRealCoefficient A i a x * (fderiv ℝ ψ x (Yau.realVec a) : ℂ) +
      fderiv ℝ (dbarRealCoefficient A i a) x (Yau.realVec a) * (ψ x : ℂ)))

theorem dbarRealCoefficient_smoothOn
    {A : X n → Matrix (Fin n) (Fin n) ℂ} {O : Set (X n)}
    (hA : MatrixSmoothOn A O) (i : Fin n) (a : Yau.RIdx n) :
    ContDiffOn ℝ ∞ (dbarRealCoefficient A i a) O :=
  contDiffOn_const.add ((hA i a.1).mul contDiffOn_const)

end Yau.LeafProofs.L21Aux

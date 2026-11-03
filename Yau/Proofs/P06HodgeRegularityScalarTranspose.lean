import Yau.Proofs.P06HodgeRegularityForwardWeak
import Yau.Proofs.P06HodgeRegularityProlongationCoefficients

/-! Scalar-principal transpose rows and the literal packing of rough
fields with their independently constructed actual weak derivatives. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux

variable {E ι α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [Fintype α] [DecidableEq ι] [DecidableEq α]

def regularityScalarTranspose (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (φ : E → ℝ) (z : E) (r c : α) : ℝ :=
  -(if r = c then ∑ i, ∑ j, regularityDirection (v j)
      (regularityDirection (v i) (fun y => q i j y * φ y)) z else 0) -
    (∑ i, regularityDirection (v i) (fun y => e1 r c i y * φ y) z) + e0 r c z * φ z

theorem regularityForwardTranspose_scalar
    (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (φ : E → ℝ) (z : E) (r c : α) :
    regularityForwardTranspose v (regularityScalarSystemA q) e1 e0 φ z r c =
      regularityScalarTranspose v q e1 e0 φ z r c := by
  classical
  have hzero (e : E) : regularityDirection e (fun _ : E => (0 : ℝ)) = 0 := by
    funext y
    simp [regularityDirection]
  by_cases hrc : r = c <;>
    simp [regularityForwardTranspose, regularityScalarTranspose,
      regularityScalarSystemA, hrc, regularityDirection]
  all_goals simp only [hzero, fderiv_zero, Pi.zero_apply, zero_apply, Finset.sum_const_zero]

def regularityProlongWeakValue (U : E → α → ℝ) (G : E → ι → α → ℝ)
    (z : E) (p : RegularityProlongIndex α ι) : ℝ :=
  match p.2 with
  | none => U z p.1
  | some i => G z i p.1

@[simp] theorem regularityProlongWeakValue_none (U : E → α → ℝ) (G : E → ι → α → ℝ)
    (z : E) (c : α) : regularityProlongWeakValue U G z (c,none) = U z c := rfl

@[simp] theorem regularityProlongWeakValue_some (U : E → α → ℝ) (G : E → ι → α → ℝ)
    (z : E) (c : α) (i : ι) : regularityProlongWeakValue U G z (c,some i) = G z i c := rfl

def regularityProlongH (v : ι → E) (e0 : α → α → E → ℝ)
    (φ : E → ℝ) (ell : ι) (r c : α) (z : E) : ℝ :=
  regularityDirection (v ell) (e0 r c) z * φ z

def regularityProlongK (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (φ : E → ℝ) (ell : ι) (r c : α) (j : ι) (z : E) : ℝ :=
  (if r = c then ∑ i, regularityDirection (v i)
    (fun y => regularityDirection (v ell) (q i j) y * φ y) z else 0) +
    regularityDirection (v ell) (e1 r c j) z * φ z

theorem regularityProlongTranspose_none_none
    (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (φ : E → ℝ) (z : E) (r c : α) :
    regularityScalarTranspose v q (regularityProlongE1 v q e1) (regularityProlongE0 v e1 e0)
      φ z (r,none) (c,none) = regularityScalarTranspose v q e1 e0 φ z r c := by
  simp only [regularityScalarTranspose, regularityProlongE1, regularityProlongE0, Prod.mk.injEq,
    and_true]

theorem regularityProlongTranspose_none_some
    (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (φ : E → ℝ) (z : E) (r c : α) (j : ι) :
    regularityScalarTranspose v q (regularityProlongE1 v q e1) (regularityProlongE0 v e1 e0)
      φ z (r,none) (c,some j) = 0 := by
  simp [regularityScalarTranspose, regularityProlongE1, regularityProlongE0, regularityDirection]

theorem regularityProlongTranspose_some_none
    (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (φ : E → ℝ) (z : E) (r c : α) (ell : ι) :
    regularityScalarTranspose v q (regularityProlongE1 v q e1) (regularityProlongE0 v e1 e0)
      φ z (r,some ell) (c,none) = regularityProlongH v e0 φ ell r c z := by
  simp [regularityScalarTranspose, regularityProlongE1, regularityProlongE0,
    regularityProlongH, regularityDirection]

end Yau.NodeProofs.P06Aux

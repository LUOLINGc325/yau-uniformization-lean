import Yau.Proofs.P06HodgeRegularityCutoff
import Yau.Proofs.P06HodgeRegularityForward

/-! Scalar-principal finite systems retain their computed lower-order
matrices. Their cutoff equation has only value sources and value fluxes. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau.LeafProofs.L03

variable {E ι α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [Fintype α]

def regularityScalarSystem (v : ι → E) (q : ι → ι → E → ℝ)
    (β : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (U : E → α → ℝ) (z : E) (r : α) : ℝ :=
  regularityScalarDiv v q (fun y => U y r) z +
    (∑ c, ∑ i, β r c i z * regularityDirection (v i) (fun y => U y c) z) +
    ∑ c, e0 r c z * U z c

def regularityScalarSystemA [DecidableEq α] (q : ι → ι → E → ℝ)
    (r c : α) (i j : ι) : E → ℝ := if r = c then q i j else 0

def regularityScalarSystemC (v : ι → E)
    (β : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (r c : α) : E → ℝ := fun z => e0 r c z - ∑ i, regularityDirection (v i) (β r c i) z

theorem regularityScalarSystem_divergence [DecidableEq α]
    (v : ι → E) (q : ι → ι → E → ℝ)
    (β : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ) (U : E → α → ℝ)
    (hβ : ∀ r c i, ContDiff ℝ ∞ (β r c i))
    (hU : ∀ c, ContDiff ℝ ∞ (fun z => U z c)) (z : E) (r : α) :
    divergenceSystemApply v (regularityScalarSystemA q) β (regularityScalarSystemC v β e0) U z r =
      regularityScalarSystem v q β e0 U z r := by
  classical
  have hdiag (c : α) (i j : ι) :
      fderiv ℝ (fun y => regularityScalarSystemA q r c i j y *
        fderiv ℝ (fun t => U t c) y (v j)) z (v i) =
      if r = c then regularityDirection (v i)
        (fun y => q i j y * regularityDirection (v j) (fun t => U t c) y) z else 0 := by
    by_cases hrc : r = c <;> simp only [regularityScalarSystemA, hrc, ite_true, ite_false,
      Pi.zero_apply, zero_mul, fderiv_fun_const, ContinuousLinearMap.zero_apply, regularityDirection]
  have hflux (c : α) (i : ι) :
      fderiv ℝ (fun y => β r c i y * U y c) z (v i) =
        regularityDirection (v i) (β r c i) z * U z c +
          β r c i z * regularityDirection (v i) (fun y => U y c) z :=
    congrFun (regularityDirection_mul (hβ r c i) (hU c) (v i)) z
  unfold divergenceSystemApply regularityScalarSystem
  simp_rw [hdiag, hflux]
  simp only [regularityScalarSystemC, sub_mul, Finset.sum_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hprincipal : (∑ c, -(∑ i, ∑ j,
      if r = c then regularityDirection (v i)
        (fun y => q i j y * regularityDirection (v j) (fun t => U t c) y) z else 0)) =
      regularityScalarDiv v q (fun y => U y r) z := by
    simp only [← Finset.sum_ite_irrel, Finset.sum_neg_distrib]
    simp [regularityScalarDiv, eq_comm]
  rw [hprincipal]
  ring

/-- The finite lower-order terms contribute only the values of U to the
cutoff forcing. This is the forward equation needed before H¹ is known. -/
theorem regularityScalarSystem_cutoff
    (v : ι → E) (q : ι → ι → E → ℝ)
    (β : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (U : E → α → ℝ) (χ : E → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hqs : ∀ i j z, q i j z = q j i z)
    (hχ : ContDiff ℝ ∞ χ) (hU : ∀ c, ContDiff ℝ ∞ (fun z => U z c))
    (z : E) (r : α) :
    regularityScalarSystem v q β e0 (fun y c => χ y * U y c) z r =
      χ z * regularityScalarSystem v q β e0 U z r +
        (regularityScalarCutoffCoeff v q χ z * U z r +
          ∑ c, ∑ i, (β r c i z * regularityDirection (v i) χ z) * U z c) +
        ∑ i, regularityDirection (v i) (regularityScalarCutoffFlux v q χ (fun y => U y r) i) z := by
  classical
  unfold regularityScalarSystem
  rw [regularityScalarDiv_cutoff v q hq hqs hχ (hU r)]
  simp_rw [regularityDirection_mul hχ (hU _) (v _)]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hβsum : (∑ c, ∑ i, β r c i z * (regularityDirection (v i) χ z * U z c)) =
      ∑ c, ∑ i, (β r c i z * regularityDirection (v i) χ z) * U z c := by
    simp only [mul_assoc]
  have hβχ : (∑ c, ∑ i, β r c i z * (χ z * regularityDirection (v i) (fun y => U y c) z)) =
      χ z * ∑ c, ∑ i, β r c i z * regularityDirection (v i) (fun y => U y c) z := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have heχ : (∑ c, e0 r c z * (χ z * U z c)) = χ z * ∑ c, e0 r c z * U z c := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [hβsum, hβχ, heχ]
  ring

/-- Scalar ellipticity lifts to every finite component rank with the same
constant, including the empty fiber. -/
theorem regularityScalarSystemA_coercive [DecidableEq α]
    (q : ι → ι → E → ℝ) (z : E) (lam : ℝ)
    (hscalar : ∀ v : ι → ℝ,
      lam * ∑ i, (v i)^2 ≤ ∑ i, ∑ j, q i j z * v j * v i)
    (ξ : ι × α → ℝ) :
    lam * ∑ p, (ξ p)^2 ≤ ∑ r, ∑ c, ∑ i, ∑ j,
      regularityScalarSystemA q r c i j z * ξ (j,c) * ξ (i,r) := by
  classical
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun (r : α) _ => hscalar (fun i => ξ (i,r)))
  have hl : (∑ r, lam * ∑ i, (ξ (i,r))^2) = lam * ∑ p, (ξ p)^2 := by
    rw [← Finset.mul_sum, Fintype.sum_prod_type, Finset.sum_comm]
  rw [hl] at h
  refine h.trans_eq ?_
  apply Finset.sum_congr rfl
  intro r _
  symm
  rw [Finset.sum_eq_single r]
  · simp only [regularityScalarSystemA, ite_true]
  · intro c _ hcr
    simp only [regularityScalarSystemA, Ne.symm hcr, ite_false, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero]
  · simp

end Yau.NodeProofs.P06Aux

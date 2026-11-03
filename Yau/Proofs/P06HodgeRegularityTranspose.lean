import Yau.Proofs.P06HodgeRegularityNondivergence
import Yau.LeafProofs.L03DivergenceLocalize

/-! Pure smooth-test transposes of the actual forward coefficients. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau.LeafProofs.L03

variable {E ι α β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [Fintype α]

def regularityForwardTranspose (v : ι → E) (a : β → α → ι → ι → E → ℝ)
    (e1 : β → α → ι → E → ℝ) (e0 : β → α → E → ℝ)
    (φ : E → ℝ) (z : E) (r : β) (c : α) : ℝ :=
  -(∑ i, ∑ j, regularityDirection (v j)
    (regularityDirection (v i) (fun y => a r c i j y * φ y)) z) -
    (∑ i, regularityDirection (v i) (fun y => e1 r c i y * φ y) z) + e0 r c z * φ z

theorem regularityForwardFormal_product
    (v : ι → E) (a : α → α → ι → ι → E → ℝ)
    (B : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j))
    (hB : ∀ r c i, ContDiff ℝ ∞ (B r c i))
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (z : E) (r c : α) :
    divergenceFormalTest v a B (regularityScalarSystemC v B e0) φ z r c =
      -(∑ i, ∑ j, regularityDirection (v j)
        (fun y => a r c i j y * regularityDirection (v i) φ y) z) -
      (∑ i, regularityDirection (v i) (fun y => B r c i y * φ y) z) + e0 r c z * φ z := by
  classical
  have hfirst (i j : ι) :
      fderiv ℝ (fun y => a r c i j y * fderiv ℝ φ y (v i)) z (v j) =
      fderiv ℝ (a r c i j) z (v j) * fderiv ℝ φ z (v i) +
        a r c i j z * fderiv ℝ (fun y => fderiv ℝ φ y (v i)) z (v j) :=
    congrFun (regularityDirection_mul (ha r c i j) (regularityDirection_contDiff hφ (v i)) (v j)) z
  have hflux (i : ι) := congrFun (regularityDirection_mul (hB r c i) hφ (v i)) z
  simp only [divergenceFormalTest, regularityScalarSystemC, regularityDirection]
  simp only [regularityDirection] at hflux
  simp_rw [hfirst, hflux, Finset.sum_add_distrib]
  simp only [sub_mul, Finset.sum_mul]
  ring

theorem regularityForwardFormal_eq_transpose
    (v : ι → E) (a : α → α → ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i))
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (z : E) (r c : α) :
    divergenceFormalTest v a (hodgeForwardB v a e1) (hodgeForwardC v a e1 e0) φ z r c =
      regularityForwardTranspose v a e1 e0 φ z r c := by
  classical
  have hB := hodgeForwardB_contDiff v a e1 ha he1
  change divergenceFormalTest v a (hodgeForwardB v a e1)
    (regularityScalarSystemC v (hodgeForwardB v a e1) e0) φ z r c = _
  rw [regularityForwardFormal_product v a (hodgeForwardB v a e1) e0 ha hB φ hφ]
  have hsplit (i : ι) :
      (fun y => hodgeForwardB v a e1 r c i y * φ y) =
      fun y => e1 r c i y * φ y +
        ∑ j, regularityDirection (v j) (a r c j i) y * φ y := by
    funext y
    simp only [hodgeForwardB, regularityDirection, add_mul, Finset.sum_mul]
  have hsplitD (i : ι) :
      regularityDirection (v i) (fun y => hodgeForwardB v a e1 r c i y * φ y) z =
      regularityDirection (v i) (fun y => e1 r c i y * φ y) z +
        ∑ j, regularityDirection (v i)
          (fun y => regularityDirection (v j) (a r c j i) y * φ y) z := by
    rw [hsplit, regularityDirection_add ((he1 r c i).mul hφ)
      (ContDiff.sum fun j _ => (regularityDirection_contDiff (ha r c j i) (v j)).mul hφ) (v i),
      regularityDirection_sum _
        (fun j => (regularityDirection_contDiff (ha r c j i) (v j)).mul hφ) (v i)]
  have hswap : (∑ i, ∑ j, regularityDirection (v i)
      (fun y => regularityDirection (v j) (a r c j i) y * φ y) z) =
      ∑ i, ∑ j, regularityDirection (v j)
        (fun y => regularityDirection (v i) (a r c i j) y * φ y) z := Finset.sum_comm
  simp_rw [hsplitD, Finset.sum_add_distrib]
  rw [hswap]
  have hpair (i j : ι) :
      regularityDirection (v j) (regularityDirection (v i) (fun y => a r c i j y * φ y)) z =
      regularityDirection (v j) (fun y => a r c i j y * regularityDirection (v i) φ y) z +
        regularityDirection (v j) (fun y => regularityDirection (v i) (a r c i j) y * φ y) z := by
    rw [regularityDirection_mul (ha r c i j) hφ (v i),
      regularityDirection_add ((regularityDirection_contDiff (ha r c i j) (v i)).mul hφ)
        ((ha r c i j).mul (regularityDirection_contDiff hφ (v i))) (v j)]
    ring
  unfold regularityForwardTranspose
  simp_rw [hpair, Finset.sum_add_distrib]
  ring

end Yau.NodeProofs.P06Aux

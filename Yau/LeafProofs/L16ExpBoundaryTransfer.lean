import Yau.LeafProofs.L16ExpBoundaryData
import Yau.LeafProofs.L16ExpBoundaryCalculus

open Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.LeafProofs.L16ExpBoundaryAux

open Yau.Parabolic Yau.ParabolicCandidates

theorem exp_lipschitz_below {x y L : ℝ} (hx : x ≤ L) (hy : y ≤ L) :
    |Real.exp x-Real.exp y| ≤ Real.exp L*|x-y| := by
  simpa only [Real.norm_eq_abs] using
    (convex_Iic L).norm_image_sub_le_of_norm_deriv_le
      (f := Real.exp) (fun z _ => Real.differentiableAt_exp)
      (by intro z hz; simpa only [Real.deriv_exp, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos z)] using Real.exp_le_exp.mpr hz) hy hx

/-- Exponentiating transfers the logarithmic boundary error with a constant
depending only on the fixed value and transformed-data bounds. -/
theorem exp_error_transfer {q P m B P₀ : ℝ} (hm : 0 < m)
    (hq : m ≤ q ∧ q ≤ B) (hP : |P| ≤ P₀) :
    |q-Real.exp P| ≤ Real.exp (max (|Real.log m|+|Real.log B|) P₀)*|Real.log q-P| := by
  have hqpos : 0 < q := hm.trans_le hq.1
  have hB : 0 < B := hqpos.trans_le hq.2
  have hv : Real.log q ≤ |Real.log m|+|Real.log B| :=
    (Real.log_le_log hqpos hq.2).trans (by linarith [le_abs_self (Real.log B),abs_nonneg (Real.log m)])
  simpa only [Real.exp_log hqpos] using exp_lipschitz_below
    (hv.trans (le_max_left _ _)) ((le_abs_self P).trans (hP.trans (le_max_right _ _)))

theorem log_error_value_bound {q P m B P₀ : ℝ} (hm : 0 < m)
    (hq : m ≤ q ∧ q ≤ B) (hP : |P| ≤ P₀) :
    |Real.log q-P| ≤ |Real.log m|+|Real.log B|+P₀ := by
  have hqpos : 0 < q := hm.trans_le hq.1
  have hlo := Real.log_le_log hm hq.1
  have hhi := Real.log_le_log hqpos hq.2
  have hv : |Real.log q| ≤ |Real.log m|+|Real.log B| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le (Real.log m),abs_nonneg (Real.log B)]
    · linarith [le_abs_self (Real.log B),abs_nonneg (Real.log m)]
  exact (abs_sub _ _).trans (add_le_add hv hP)

/-- Only the boundary values of the prescribed extension need be positive. -/
theorem fixed_log_boundary_agreement {n : ℕ} {O : Set (Space n)}
    {T m B : ℝ} (hT : 0 ≤ T) (hm : 0 < m)
    {p q : Point n → ℝ} {ℓ : ℝ → ℝ}
    (hℓ : EqOn ℓ Real.log (Ioo (m/2) (B+1)))
    (hbound : ∀ z ∈ cylinder (closure O) 0 T, m ≤ q z ∧ q z ≤ B)
    (hdata : DirichletData O T q p) :
    DirichletData O T q (fun z => Real.exp (ℓ (p z))) ∧
      DirichletData O T (fun z => Real.log (q z)-ℓ (p z)) (fun _ => 0) := by
  have hpoint (z : Point n) (hz : z ∈ cylinder (closure O) 0 T) (heq : q z = p z) :
      ℓ (p z) = Real.log (q z) := by
    rw [← heq]
    apply hℓ
    constructor <;> linarith [(hbound z hz).1,(hbound z hz).2]
  have hi (x : Space n) (hx : x ∈ closure O) : ℓ (p (x,0)) = Real.log (q (x,0)) :=
    hpoint (x,0) ⟨hx,le_rfl,hT⟩ (hdata.1 x hx)
  have hl (x : Space n) (hx : x ∈ frontier O) (t : ℝ) (ht : t ∈ Icc 0 T) :
      ℓ (p (x,t)) = Real.log (q (x,t)) :=
    hpoint (x,t) ⟨frontier_subset_closure hx,ht⟩ (hdata.2 x hx t ht)
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro x hx
    change q (x,0) = Real.exp (ℓ (p (x,0)))
    rw [hi x hx,Real.exp_log (hm.trans_le (hbound (x,0) ⟨hx,le_rfl,hT⟩).1)]
  · intro x hx t ht
    change q (x,t) = Real.exp (ℓ (p (x,t)))
    rw [hl x hx t ht,Real.exp_log (hm.trans_le
      (hbound (x,t) ⟨frontier_subset_closure hx,ht⟩).1)]
  · intro x hx
    change Real.log (q (x,0))-ℓ (p (x,0)) = 0
    rw [hi x hx,sub_self]
  · intro x hx t ht
    change Real.log (q (x,t))-ℓ (p (x,t)) = 0
    rw [hl x hx t ht,sub_self]

/-- The logarithmic error is continuous on the whole closed cylinder. -/
theorem log_error_continuous {n : ℕ} {Q : Set (Point n)} {q P : Point n → ℝ}
    {m : ℝ} (hm : 0 < m) (hq : ContinuousOn q Q) (hP : ContinuousOn P Q)
    (hbound : ∀ z ∈ Q, m ≤ q z) :
    ContinuousOn (fun z => Real.log (q z)-P z) Q :=
  (hq.log (fun z hz => (hm.trans_le (hbound z hz)).ne')).sub hP

end Yau.LeafProofs.L16ExpBoundaryAux

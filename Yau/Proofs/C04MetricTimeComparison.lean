import Yau.Proofs.C04MatrixForms

/-! Pointwise time comparison from the actual matrix metric ODE. -/

noncomputable section
open scoped Matrix ComplexOrder
open Set

namespace Yau.Proofs.C04Aux
open Yau Blueprint Matrix
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem scalar_metric_decay {f r : ℝ → ℝ} {a b A : ℝ}
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (-r t) t)
    (hr : ∀ t ∈ Icc a b, 0 ≤ r t)
    (hupper : ∀ t ∈ Icc a b, r t ≤ A * f t)
    {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (huv : u ≤ v) :
    Real.exp (-A * (v - u)) * f u ≤ f v ∧ f v ≤ f u := by
  have hanti : AntitoneOn f (Icc a b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
    · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt
    · exact fun t ht => neg_nonpos.mpr (hr t (interior_subset ht))
  have hmono : MonotoneOn (fun t => Real.exp (A * t) * f t) (Icc a b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    · intro t ht
      exact (((continuousAt_id.const_mul A).rexp).mul (hd t ht).continuousAt).continuousWithinAt
    · intro t ht
      exact ((((hasDerivAt_id t).const_mul A).exp).mul (hd t (interior_subset ht))).hasDerivWithinAt
    · intro t ht
      have hh := hupper t (interior_subset ht)
      have he := Real.exp_pos (A * t)
      have hp := mul_nonneg he.le (sub_nonneg.mpr hh)
      simp only [id_eq, mul_one]
      nlinarith
  refine ⟨?_, hanti hu hv huv⟩
  have hh := mul_le_mul_of_nonneg_left (hmono hu hv huv) (Real.exp_pos (-A * v)).le
  rw [← mul_assoc, ← Real.exp_add, ← mul_assoc, ← Real.exp_add] at hh
  have h₁ : -A * v + A * u = -A * (v - u) := by ring
  have h₂ : -A * v + A * v = 0 := by ring
  simpa only [h₁, h₂, Real.exp_zero, one_mul] using hh

theorem scalar_metric_interval_comparison {f r : ℝ → ℝ} {a b A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (-r t) t)
    (hr : ∀ t ∈ Icc a b, 0 ≤ r t)
    (hupper : ∀ t ∈ Icc a b, r t ≤ A * f t)
    {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) :
    f u ≤ Real.exp (A * (b - a)) * f v := by
  by_cases huv : u ≤ v
  · have hh := (scalar_metric_decay hd hr hupper hu hv huv).1
    have hm := mul_le_mul_of_nonneg_left hh (Real.exp_pos (A * (v - u))).le
    have hexp : Real.exp (A * (v - u)) * Real.exp (-A * (v - u)) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1 <;> ring
    rw [← mul_assoc, hexp, one_mul] at hm
    exact hm.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (by linarith [hu.1, hv.2] : v - u ≤ b - a) hA)) (hf v hv))
  · have hmono := (scalar_metric_decay hd hr hupper hv hu (le_of_not_ge huv)).2
    have hone : 1 ≤ Real.exp (A * (b - a)) := Real.one_le_exp (mul_nonneg hA (by linarith [hu.1, hu.2]))
    exact hmono.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hone (hf v hv))

theorem matrix_metric_interval_comparison (H R : ℝ → Herm n) {a b A : ℝ} (hA : 0 ≤ A)
    (hH : ∀ t ∈ Icc a b, (H t).PosDef)
    (hd : ∀ t ∈ Icc a b, ∀ i j, HasDerivAt (fun s => H s i j) (-(R t) i j) t)
    (hr : ∀ t ∈ Icc a b, (R t).PosSemidef)
    (hupper : ∀ t ∈ Icc a b, HermLE (R t) ((A : ℂ) • H t))
    {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) :
    HermLE (H u) ((Real.exp (A * (b - a)) : ℂ) • H v) := by
  have hself : IsSelfAdjoint ((Real.exp (A * (b - a)) : ℝ) : ℂ) :=
    Complex.conj_ofReal _
  apply HermLE_of_matrixForm_le (hH u hu).isHermitian ((hH v hv).isHermitian.smul hself)
  intro w
  rw [matrixForm_real_smul]
  apply scalar_metric_interval_comparison (f := fun t => Blueprint.Alignment.Y03Proof.matrixForm (H t) w)
    (r := fun t => Blueprint.Alignment.Y03Proof.matrixForm (R t) w) (a := a) (b := b) hA
  · intro t ht
    exact (hH t ht).posSemidef.re_dotProduct_nonneg w
  · intro t ht
    simpa only [matrixForm_neg] using
      Blueprint.Alignment.Y03Proof.matrixForm_hasDerivAt H (-(R t)) (hd t ht) w
  · intro t ht
    exact (hr t ht).re_dotProduct_nonneg w
  · intro t ht
    simpa only [matrixForm_real_smul] using matrixForm_order (hupper t ht) w
  · exact hu
  · exact hv

theorem fixed_domain_metric_comparison {α : Type*} (H R : α → ℝ → Herm n)
    (D : Set α) {θ A : ℝ} (hθ : 0 ≤ θ) (hA : 0 ≤ A)
    (hH : ∀ x ∈ D, ∀ t ∈ Icc (-2 * θ) (2 * θ), (H x t).PosDef)
    (hd : ∀ x ∈ D, ∀ t ∈ Icc (-2 * θ) (2 * θ), ∀ i j,
      HasDerivAt (fun s => H x s i j) (-(R x t) i j) t)
    (hr : ∀ x ∈ D, ∀ t ∈ Icc (-2 * θ) (2 * θ), (R x t).PosSemidef)
    (hupper : ∀ x ∈ D, ∀ t ∈ Icc (-2 * θ) (2 * θ),
      HermLE (R x t) ((A : ℂ) • H x t)) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ ∀ x ∈ D, ∀ u ∈ Icc (-2 * θ) (2 * θ),
      ∀ v ∈ Icc (-2 * θ) (2 * θ), HermLE (H x u) (((Λ ^ 2 : ℝ) : ℂ) • H x v) := by
  refine ⟨Real.exp (2 * θ * A), Real.one_le_exp (by positivity), ?_⟩
  intro x hx u hu v hv
  have hexp : Real.exp (A * (2 * θ - (-2 * θ))) = Real.exp (2 * θ * A) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simpa only [hexp] using matrix_metric_interval_comparison (H x) (R x) hA
    (hH x hx) (hd x hx) (hr x hx) (hupper x hx) hu hv

end Yau.Proofs.C04Aux

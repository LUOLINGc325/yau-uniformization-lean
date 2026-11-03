import Yau.LeafProofs.L16ExpBoundaryDefiningBarrier
import Yau.LeafProofs.L16ExpBoundaryGeometry

open Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.LeafProofs.L16ExpBoundaryAux

open Yau.Parabolic Yau.ParabolicCandidates

theorem definingFunction_coordinate_jet_bounds {n : ℕ} {s : Space n → ℝ}
    {x : Space n} {M₁ M₂ : ℝ}
    (h₁ : ‖fderiv ℝ s x‖ ≤ M₁) (h₂ : ‖fderiv ℝ (fderiv ℝ s) x‖ ≤ M₂) :
    (∀ i, |d s x i| ≤ M₁) ∧
      ∀ i j, |fderiv ℝ (fderiv ℝ s) x (Yau.realVec i) (Yau.realVec j)| ≤ M₂ := by
  constructor
  · intro i
    have h := (fderiv ℝ s x).le_opNorm (Yau.realVec i)
    simp only [Real.norm_eq_abs,L16Aux.realVec_norm,mul_one] at h
    exact h.trans h₁
  · intro i j
    have h := ((fderiv ℝ (fderiv ℝ s) x (Yau.realVec i)).le_opNorm (Yau.realVec j)).trans
      (mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ s) x).le_opNorm (Yau.realVec i))
        (norm_nonneg _))
    simp only [Real.norm_eq_abs,L16Aux.realVec_norm,mul_one] at h
    exact h.trans h₂

theorem definingFunction_contraction_abs_bound {n : ℕ} {s : Space n → ℝ}
    {x : Space n} {M₁ M₂ A₀ b₀ : ℝ} {A : Mat n} {β : Yau.RIdx n → ℝ}
    (hA₀ : 0 ≤ A₀) (hb₀ : 0 ≤ b₀)
    (h₁ : ‖fderiv ℝ s x‖ ≤ M₁) (h₂ : ‖fderiv ℝ (fderiv ℝ s) x‖ ≤ M₂)
    (hA : ∀ i j, |A i j| ≤ A₀) (hβ : ∀ i, |β i| ≤ b₀) :
    |(∑ i, ∑ j, A i j*fderiv ℝ (fderiv ℝ s) x (Yau.realVec i) (Yau.realVec j)) +
        ∑ i, β i*d s x i| ≤
      (∑ _i : Yau.RIdx n, ∑ _j : Yau.RIdx n, A₀*M₂) +
        ∑ _i : Yau.RIdx n, b₀*M₁ := by
  have hj := definingFunction_coordinate_jet_bounds h₁ h₂
  apply (abs_add_le _ _).trans
  apply add_le_add
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j hjmem
    rw [abs_mul]
    exact mul_le_mul (hA i j) (hj.2 i j) (abs_nonneg _) hA₀
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    rw [abs_mul]
    exact mul_le_mul (hβ i) (hj.1 i) (abs_nonneg _) hb₀

/-- The positive gradient term dominates the bounded lower-order contraction. -/
theorem definingBarrier_operator_lower_bound {n : ℕ} {s : Space n → ℝ}
    {x : Space n} {κ ν a₀ S₀ Lρ : ℝ} (hs : ContDiffAt ℝ 2 s x)
    (hκ : 0 < κ) (hν : 0 < ν) (ha₀ : 0 < a₀)
    (hgap : 0 < κ*ν*a₀^2-Lρ)
    (hgrad : a₀ ≤ ‖fderiv ℝ s x‖) (hsup : s x ≤ S₀)
    {A : Mat n} {β : Yau.RIdx n → ℝ}
    (hquad : ∀ v : Yau.RIdx n → ℝ, ν*(∑ i, (v i)^2) ≤ ∑ i, ∑ j, A i j*v i*v j)
    (hL : |(∑ i, ∑ j, A i j*fderiv ℝ (fderiv ℝ s) x (Yau.realVec i) (Yau.realVec j)) +
        ∑ i, β i*d s x i| ≤ Lρ) :
    κ*Real.exp (-κ*S₀)*(κ*ν*a₀^2-Lρ) ≤
      -(∑ i, ∑ j, A i j*fderiv ℝ (fderiv ℝ (definingBarrier s κ)) x
        (Yau.realVec i) (Yau.realVec j)) - ∑ i, β i*d (definingBarrier s κ) x i := by
  rw [definingBarrier_operator_identity hs]
  have hgradSq : a₀^2 ≤ ∑ i, (d s x i)^2 := by
    rw [← defining_data_gradient_coordinates]
    exact pow_le_pow_left₀ ha₀.le hgrad 2
  have hq : ν*a₀^2 ≤ ∑ i, ∑ j, A i j*d s x i*d s x j :=
    (mul_le_mul_of_nonneg_left hgradSq hν.le).trans (hquad (fun i => d s x i))
  have hl := (abs_le.mp hL).2
  have hinner : κ*ν*a₀^2-Lρ ≤
      κ*(∑ i, ∑ j, A i j*d s x i*d s x j) -
        (∑ i, ∑ j, A i j*fderiv ℝ (fderiv ℝ s) x (Yau.realVec i) (Yau.realVec j)) -
        ∑ i, β i*d s x i := by
    nlinarith [mul_le_mul_of_nonneg_left hq hκ.le]
  have he : κ*Real.exp (-κ*S₀) ≤ κ*Real.exp (-κ*s x) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hκ.le
  exact mul_le_mul he hinner hgap.le (by positivity)

/-- Both exponential constants are fixed from the ellipticity and defining
function bounds before the actual coefficient fields are introduced. -/
theorem exists_definingBarrier_constants {ν a₀ S₀ Lρ : ℝ}
    (hν : 0 < ν) (ha₀ : 0 < a₀) (hLρ : 0 ≤ Lρ) :
    ∃ κ μ : ℝ, 0 < κ ∧ 0 < μ ∧ 0 < κ*ν*a₀^2-Lρ ∧
      μ = κ*Real.exp (-κ*S₀)*(κ*ν*a₀^2-Lρ) := by
  let c : ℝ := ν*a₀^2
  have hc : 0 < c := by dsimp [c]; positivity
  let κ : ℝ := 1+(2*Lρ+1)/c
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκc : κ*c = c+2*Lρ+1 := by dsimp [κ]; field_simp; ring
  have hgap : 0 < κ*ν*a₀^2-Lρ := by
    have heq : κ*ν*a₀^2 = κ*c := by dsimp [c]; ring
    rw [heq,hκc]
    linarith
  exact ⟨κ,κ*Real.exp (-κ*S₀)*(κ*ν*a₀^2-Lρ),hκ,by positivity,hgap,rfl⟩

end Yau.LeafProofs.L16ExpBoundaryAux

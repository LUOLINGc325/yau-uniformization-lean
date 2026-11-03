import Yau.Proofs.P06CylinderRegularityJointEstimate

/-! Fixed finite linear combinations retain the proved full joint jet
estimate. This includes every original alternating-form component. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau.Parabolic

theorem exists_joint_linear_jet_constant {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (e1 : α → α → Yau.RIdx n → Point n → ℝ) (e0 : α → α → Point n → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hcq : ∀ i j, HasCompactSupport (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (hce1 : ∀ r c i, HasCompactSupport (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c)) (hce0 : ∀ r c, HasCompactSupport (e0 r c))
    {Q K : Set (Point n)} (hQ : IsOpen Q) (hK : IsCompact K) (hKQ : K ⊆ Q)
    (lam upper A : ℝ) (hlam : 0 < lam) (hA : 0 ≤ A)
    (hEll : Elliptic Q (heatPrincipal q) lam upper)
    (ha : ∀ p ∈ Q, ∀ i j, |heatPrincipal q p i j| ≤ A) (ℓ : α → ℝ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : Point n → α → ℝ,
      (∀ r, ContDiff ℝ ∞ (fun p => U p r)) → heatEquation q e1 e0 Q U →
      IntegrableOn (valueSquare U) Q → ∀ p ∈ K,
      ‖iteratedFDeriv ℝ m (fun p => ∑ r, ℓ r * U p r) p‖^2 ≤
        C * ∫ p in Q, valueSquare U p := by
  classical
  choose C hC hEst using fun r => exists_joint_jet_constant q e1 e0 hq hcq he1 hce1 he0 hce0
    hQ hK hKQ lam upper A hlam hA hEll ha r m
  let B := ∑ r, (ℓ r)^2 * C r
  have hB : 0 ≤ B := Finset.sum_nonneg fun r _ => mul_nonneg (sq_nonneg _) (hC r).le
  refine ⟨1+(Fintype.card α : ℝ)*B,by positivity,?_⟩
  intro U hU hPDE hUI p hp
  have hSum : iteratedFDeriv ℝ m (fun p => ∑ r, ℓ r * U p r) p =
      ∑ r, ℓ r • iteratedFDeriv ℝ m (fun p => U p r) p := by
    change iteratedFDeriv ℝ m (fun p => ∑ r, ℓ r • U p r) p = _
    rw [iteratedFDeriv_fun_sum_apply (fun r _ =>
      ((hU r).const_smul (ℓ r)).contDiffAt.of_le (by simp))]
    apply Finset.sum_congr rfl
    intro r _
    exact iteratedFDeriv_const_smul_apply' ((hU r).contDiffAt.of_le (by simp))
  rw [hSum]
  have hNorm := norm_sum_le (s := Finset.univ)
    (f := fun r => ℓ r • iteratedFDeriv ℝ m (fun p => U p r) p)
  have hSq := pow_le_pow_left₀ (norm_nonneg _) hNorm 2
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : α => (1 : ℝ))
    (fun r => ‖ℓ r • iteratedFDeriv ℝ m (fun p => U p r) p‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hCS
  have hEach (r : α) : ‖ℓ r • iteratedFDeriv ℝ m (fun p => U p r) p‖^2 ≤
      (ℓ r)^2 * C r * (∫ p in Q, valueSquare U p) := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    exact (mul_le_mul_of_nonneg_left (hEst r U hU hPDE hUI p hp) (sq_nonneg _)).trans_eq (by ring)
  have hAll := Finset.sum_le_sum (s := Finset.univ) (fun r _ => hEach r)
  rw [← Finset.sum_mul] at hAll
  have hNonneg : 0 ≤ ∫ p in Q, valueSquare U p := integral_nonneg fun p => valueSquare_nonneg U p
  have hFinal := mul_le_mul_of_nonneg_left hAll (show (0 : ℝ) ≤ Fintype.card α by positivity)
  dsimp only [B] at hB ⊢
  nlinarith

end Yau.NodeProofs.P06Aux.CylinderReg

import Yau.Proofs.P06SmallTimeCylinderCylinders

/-! Explicit small-time interior cylinder estimates for the original
scalar-principal finite system.  All constants precede τ and the solution. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.SmallTimeCylinder
open Yau.Parabolic Yau.LeafProofs.L16Aux CylinderReg
variable {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]

theorem exists_small_time_cylinder_jet_constant
    (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (e1 : α → α → Yau.RIdx n → Point n → ℝ) (e0 : α → α → Point n → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hcq : ∀ i j, HasCompactSupport (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (hce1 : ∀ r c i, HasCompactSupport (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c)) (hce0 : ∀ r c, HasCompactSupport (e0 r c))
    {O K : Set (Space n)} (hO : IsOpen O) (hcO : IsCompact (closure O))
    (hK : IsCompact K) (hKO : K ⊆ O)
    (lam upper A : ℝ) (hlam : 0 < lam) (hA : 0 ≤ A)
    (hEll : Elliptic (O ×ˢ Set.Ioo (0 : ℝ) 2) (heatPrincipal q) lam upper)
    (ha : ∀ p ∈ O ×ˢ Set.Ioo (0 : ℝ) 2, ∀ i j, |heatPrincipal q p i j| ≤ A)
    (r : α) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℝ), 0 < τ → τ ≤ 1 →
      ∀ U : Point n → α → ℝ,
      (∀ r, ContDiff ℝ ∞ (fun p => U p r)) →
      heatEquation q e1 e0 (O ×ˢ Set.Ioo (τ / 4) (2 * τ)) U →
      ∀ p ∈ K ×ˢ Set.Icc (τ / 2) (3 * τ / 2),
      ‖iteratedFDeriv ℝ m (fun p => U p r) p‖ ^ 2 ≤
        (C / τ ^ (6 * (m + Fintype.card (ParabolicJointIdx n)))) *
          ∫ p in O ×ˢ Set.Ioo (τ / 4) (2 * τ), valueSquare U p := by
  let Q0 := O ×ˢ Set.Ioo (1 / 4 : ℝ) 2
  let K0 := K ×ˢ Set.Icc (1 / 2 : ℝ) (3 / 2 : ℝ)
  have hQ0 : IsOpen Q0 := hO.prod isOpen_Ioo
  have hK0 : IsCompact K0 := hK.prod isCompact_Icc
  have hKQ : K0 ⊆ Q0 := by
    intro p hp
    exact ⟨hKO hp.1, by linarith [hp.2.1], by linarith [hp.2.2]⟩
  have hSub (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
      timeScale τ hτ.ne' '' Q0 ⊆ O ×ˢ Set.Ioo (0 : ℝ) 2 := by
    rw [show timeScale τ hτ.ne' '' Q0 = O ×ˢ Set.Ioo (τ / 4) (2 * τ) from
      timeScale_outer_cylinder O τ hτ]
    exact outer_cylinder_subset O τ hτ hτ1
  have hEllτ : ∀ (τ : ℝ) (hτ : 0 < τ), τ ≤ 1 →
      Elliptic (timeScale τ hτ.ne' '' Q0) (heatPrincipal q) lam upper := by
    intro τ hτ hτ1
    exact ⟨hEll.1, hEll.2.1, fun p hp => hEll.2.2 p (hSub τ hτ hτ1 hp)⟩
  obtain ⟨C, hC, hEst⟩ := exists_small_time_joint_jet_constant q e1 e0 hq hcq
    he1 hce1 he0 hce0 hQ0 hK0 hKQ lam upper A hlam hA hEllτ
      (fun τ hτ hτ1 p hp => ha p (hSub τ hτ hτ1 hp)) r m
  refine ⟨C, hC, ?_⟩
  intro τ hτ hτ1 U hU hPDE p hp
  have hOuter : timeScale τ hτ.ne' '' Q0 = O ×ˢ Set.Ioo (τ / 4) (2 * τ) :=
    timeScale_outer_cylinder O τ hτ
  have hPDE' : heatEquation q e1 e0 (timeScale τ hτ.ne' '' Q0) U := by
    rw [hOuter]
    exact hPDE
  have hInt : IntegrableOn (valueSquare U) (timeScale τ hτ.ne' '' Q0) := by
    rw [hOuter]
    exact valueSquare_integrableOn_cylinder O hcO U hU (τ / 4) (2 * τ)
  have hh := hEst τ hτ hτ1 U hU hPDE' hInt p (mem_timeScale_inner_cylinder K τ hτ hp)
  rwa [hOuter] at hh

/-- ST in local spatial L² norm form.  The norm constant, like the squared
jet constant, is fixed before τ, the solution, and the numerical norm bound. -/
theorem exists_small_time_cylinder_norm_constant
    (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (e1 : α → α → Yau.RIdx n → Point n → ℝ) (e0 : α → α → Point n → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hcq : ∀ i j, HasCompactSupport (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (hce1 : ∀ r c i, HasCompactSupport (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c)) (hce0 : ∀ r c, HasCompactSupport (e0 r c))
    {O K : Set (Space n)} (hO : IsOpen O) (hcO : IsCompact (closure O))
    (hK : IsCompact K) (hKO : K ⊆ O)
    (lam upper A : ℝ) (hlam : 0 < lam) (hA : 0 ≤ A)
    (hEll : Elliptic (O ×ˢ Set.Ioo (0 : ℝ) 2) (heatPrincipal q) lam upper)
    (ha : ∀ p ∈ O ×ˢ Set.Ioo (0 : ℝ) 2, ∀ i j, |heatPrincipal q p i j| ≤ A)
    (r : α) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℝ), 0 < τ → τ ≤ 1 →
      ∀ U : Point n → α → ℝ,
      (∀ r, ContDiff ℝ ∞ (fun p => U p r)) →
      heatEquation q e1 e0 (O ×ˢ Set.Ioo (τ / 4) (2 * τ)) U →
      ∀ L : ℝ, 0 ≤ L →
      (∀ s ∈ Set.Ioo (τ / 4) (2 * τ), (∫ z in O, valueSquare U (z,s)) ≤ L ^ 2) →
      ∀ p ∈ K ×ˢ Set.Icc (τ / 2) (3 * τ / 2),
      ‖iteratedFDeriv ℝ m (fun p => U p r) p‖ ≤
        (C / τ ^ (3 * (m + Fintype.card (ParabolicJointIdx n)))) * L := by
  obtain ⟨C, hC, hEst⟩ := exists_small_time_cylinder_jet_constant q e1 e0 hq hcq
    he1 hce1 he0 hce0 hO hcO hK hKO lam upper A hlam hA hEll ha r m
  refine ⟨2 * C + 1, by positivity, ?_⟩
  intro τ hτ hτ1 U hU hPDE L hL hSlice p hp
  let J := m + Fintype.card (ParabolicJointIdx n)
  have hJet := hEst τ hτ hτ1 U hU hPDE p hp
  have hEnergy := cylinder_energy_le_of_slice_bound O hcO U hU τ hτ L hSlice
  have hEnergy' : (∫ p in O ×ˢ Set.Ioo (τ / 4) (2 * τ), valueSquare U p) ≤ 2 * L ^ 2 :=
    hEnergy.trans (mul_le_mul_of_nonneg_right (by linarith : 2 * τ ≤ 2) (sq_nonneg L))
  have hSq := hJet.trans (mul_le_mul_of_nonneg_left hEnergy'
    (div_nonneg hC.le (pow_nonneg hτ.le _)))
  change ‖iteratedFDeriv ℝ m (fun p => U p r) p‖ ≤ ((2 * C + 1) / τ ^ (3 * J)) * L
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
    (div_nonneg (by positivity) (pow_nonneg hτ.le _)) hL)).mp
  have hPow : (τ ^ (3 * J)) ^ 2 = τ ^ (6 * J) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [mul_pow, div_pow, hPow]
  calc
    _ ≤ (2 * C / τ ^ (6 * J)) * L ^ 2 := by convert hSq using 1 <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (by nlinarith) (pow_nonneg hτ.le _)) (sq_nonneg L)

end Yau.NodeProofs.P06Aux.SmallTimeCylinder

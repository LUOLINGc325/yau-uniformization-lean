import Yau.Proofs.P06SmallTimeCylinderSpatialEnergy
import Yau.Proofs.P06SmallTimeCylinderWords

/-! A fixed coefficient map for the unlocalized joint word is bounded on
one compact hull containing all time dilations of the inner buffer. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.SmallTimeCylinder
open Yau.Parabolic Yau.LeafProofs.L16Aux CylinderReg
variable {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]

theorem exists_small_time_word_local_energy_constant
    (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (e1 : α → α → Yau.RIdx n → Point n → ℝ) (e0 : α → α → Point n → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hcq : ∀ i j, HasCompactSupport (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (hce1 : ∀ r c i, HasCompactSupport (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c)) (hce0 : ∀ r c, HasCompactSupport (e0 r c))
    {Q K : Set (Point n)} (hQ : IsOpen Q) (hK : IsCompact K) (hKQ : K ⊆ Q)
    (lam upper A : ℝ) (hlam : 0 < lam) (hA : 0 ≤ A)
    (hEll : ∀ (τ : ℝ) (hτ : 0 < τ), τ ≤ 1 →
      Elliptic (timeScale τ hτ.ne' '' Q) (heatPrincipal q) lam upper)
    (ha : ∀ (τ : ℝ) (hτ : 0 < τ), τ ≤ 1 →
      ∀ p ∈ timeScale τ hτ.ne' '' Q, ∀ i j, |heatPrincipal q p i j| ≤ A)
    (r : α) (w : List (ParabolicJointIdx n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℝ) (hτ : 0 < τ), τ ≤ 1 →
      ∀ U : Point n → α → ℝ,
      (∀ r, ContDiff ℝ ∞ (fun p => U p r)) →
      heatEquation q e1 e0 (timeScale τ hτ.ne' '' Q) U →
      IntegrableOn (valueSquare U) (timeScale τ hτ.ne' '' Q) →
      (∫ p in timeScale τ hτ.ne' '' K,
        (regularityCoefficientWord parabolicJointVec w (fun p => U p r) p) ^ 2) ≤
        (C / τ ^ (4 * w.length)) * ∫ p in timeScale τ hτ.ne' '' Q, valueSquare U p := by
  classical
  have hMap := wordJetCLM_contDiff q e1 e0 hq hcq he1 hce1 he0 hce0
    (χ := fun _ => 1) contDiff_const r w
  obtain ⟨b, hb⟩ := (dilationHull_isCompact hK).bddAbove_image hMap.continuous.norm.continuousOn
  let B := max b 0
  have hB : 0 ≤ B := le_max_right _ _
  obtain ⟨C, hC, hEnergy⟩ := exists_small_time_spatial_energy_constant q hq hcq
    (jointJetDepth w) α e1 e0 he1 hce1 he0 hce0 hQ hK hKQ lam upper A hlam hA hEll ha
  refine ⟨1 + B ^ 2 * C, by positivity, ?_⟩
  intro τ hτ hτ1 U hU hPDE hUI
  let T := timeScale (n := n) τ hτ.ne'
  have hKτ : IsCompact (T '' K) := hK.image T.continuous
  have hBound : ∀ p ∈ T '' K,
      ‖wordJetCLM q e1 e0 (fun _ => 1) r w p‖ ≤ B := by
    intro p hp
    exact (hb (Set.mem_image_of_mem _ (timeScale_image_subset_dilationHull τ hτ hτ1 hp))).trans
      (le_max_left b 0)
  have hIntWord : IntegrableOn
      (fun p => (regularityCoefficientWord parabolicJointVec w (fun p => U p r) p) ^ 2)
      (T '' K) :=
    ((regularityCoefficientWord_contDiff parabolicJointVec (hU r) w).pow 2).continuous.continuousOn
      |>.integrableOn_compact hKτ
  have hIntJet : IntegrableOn
      (valueSquare (jetValue (fun i => (Yau.realVec i,0)) U (jointJetDepth w))) (T '' K) :=
    (ContDiff.sum (fun c _ => (jetValue_contDiff _ hU _ c).pow 2)).continuous.continuousOn
      |>.integrableOn_compact hKτ
  have hPoint : ∀ p ∈ T '' K,
      (regularityCoefficientWord parabolicJointVec w (fun p => U p r) p) ^ 2 ≤
        B ^ 2 * valueSquare (jetValue (fun i => (Yau.realVec i,0)) U (jointJetDepth w)) p := by
    intro p hp
    have hActual := wordJetCLM_actual q e1 e0 (T.toHomeomorph.isOpenMap _ hQ) U hq hcq
      he1 hce1 he0 hce0 (χ := fun _ => 1) contDiff_const hU hPDE r w (Set.image_mono hKQ hp)
    simp only [one_mul] at hActual
    rw [hActual]
    have hOp := (wordJetCLM q e1 e0 (fun _ => 1) r w p).le_opNorm
      (jetValue (fun i => (Yau.realVec i,0)) U (jointJetDepth w) p)
    have hOpB := hOp.trans (mul_le_mul_of_nonneg_right (hBound p hp) (norm_nonneg _))
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hOpB 2
    simp only [Real.norm_eq_abs, sq_abs, mul_pow] at hsq
    exact hsq.trans (mul_le_mul_of_nonneg_left
      (pi_norm_sq_le_sum_sq (jetValue (fun i => (Yau.realVec i,0)) U (jointJetDepth w) p))
      (sq_nonneg B))
  have hLocal := setIntegral_mono_on hIntWord (hIntJet.const_mul (B ^ 2)) hKτ.measurableSet hPoint
  rw [integral_const_mul] at hLocal
  have hTotal := hLocal.trans (mul_le_mul_of_nonneg_left (hEnergy τ hτ hτ1 U hU hPDE hUI)
    (sq_nonneg B))
  have hDepth : 2 * jointJetDepth w = 4 * w.length := by rw [jointJetDepth_eq]; omega
  rw [hDepth] at hTotal
  have hNonneg : 0 ≤ ∫ p in T '' Q, valueSquare U p :=
    integral_nonneg (fun p => valueSquare_nonneg U p)
  calc
    _ ≤ (B ^ 2 * C / τ ^ (4 * w.length)) * ∫ p in T '' Q, valueSquare U p := by
      convert hTotal using 1 <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (by linarith) (pow_nonneg hτ.le _)) hNonneg

end Yau.NodeProofs.P06Aux.SmallTimeCylinder

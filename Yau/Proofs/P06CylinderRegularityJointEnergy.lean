import Yau.Proofs.P06CylinderRegularityJointWords
import Yau.Proofs.P06CylinderRegularitySpatialIteration

/-! Every actual finite joint word of a fixed compact localization is
controlled by the local value L² norm of the original solution. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem pi_norm_sq_le_sum_sq {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    ‖v‖^2 ≤ ∑ i, (v i)^2 := by
  classical
  let S := ∑ i, (v i)^2
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hNorm : ‖v‖ ≤ Real.sqrt S := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg S)).mpr
    intro i
    have hi : (v i)^2 ≤ S := Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
    rw [Real.norm_eq_abs]
    nlinarith [Real.sq_sqrt hS, Real.sqrt_nonneg S, sq_abs (v i), abs_nonneg (v i)]
  have h := pow_le_pow_left₀ (norm_nonneg _) hNorm 2
  rwa [Real.sq_sqrt hS] at h

theorem exists_joint_word_energy_constant {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (e1 : α → α → Yau.RIdx n → Point n → ℝ) (e0 : α → α → Point n → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hcq : ∀ i j, HasCompactSupport (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (hce1 : ∀ r c i, HasCompactSupport (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c)) (hce0 : ∀ r c, HasCompactSupport (e0 r c))
    {Q : Set (Point n)} (hQ : IsOpen Q) (χ : Point n → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hχQ : tsupport χ ⊆ Q)
    (lam upper A : ℝ) (hlam : 0 < lam) (hA : 0 ≤ A)
    (hEll : Elliptic Q (heatPrincipal q) lam upper)
    (ha : ∀ p ∈ Q, ∀ i j, |heatPrincipal q p i j| ≤ A)
    (r : α) (w : List (ParabolicJointIdx n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : Point n → α → ℝ,
      (∀ r, ContDiff ℝ ∞ (fun p => U p r)) → heatEquation q e1 e0 Q U →
      IntegrableOn (valueSquare U) Q →
      (∫ p, (regularityCoefficientWord parabolicJointVec w (fun p => χ p * U p r) p)^2) ≤
        C * ∫ p in Q, valueSquare U p := by
  classical
  have hC := wordJetCLM_contDiff q e1 e0 hq hcq he1 hce1 he0 hce0 hχ r w
  obtain ⟨b,hb⟩ := hcχ.bddAbove_image hC.continuous.norm.continuousOn
  let B := max b 0
  have hB : 0 ≤ B := le_max_right _ _
  have hBound : ∀ p ∈ tsupport χ, ‖wordJetCLM q e1 e0 χ r w p‖ ≤ B := by
    intro p hp
    exact (hb (Set.mem_image_of_mem _ hp)).trans (le_max_left _ _)
  obtain ⟨C,hCpos,hEnergy⟩ := exists_spatial_energy_constant q hq hcq (jointJetDepth w) α e1 e0
    he1 hce1 he0 hce0 hQ hcχ hχQ lam upper A hlam hA hEll ha
  refine ⟨1+B^2*C,by positivity,?_⟩
  intro U hU hPDE hUI
  let f : Point n → ℝ := fun p => χ p * U p r
  have hf : ContDiff ℝ ∞ f := hχ.mul (hU r)
  have hcf : HasCompactSupport f := hcχ.mul_right
  have hWord := regularityCoefficientWord_regular parabolicJointVec hf hcf w
  have hSupport : tsupport (regularityCoefficientWord parabolicJointVec w f) ⊆ tsupport χ :=
    hWord.2.2.trans tsupport_mul_subset_left
  have hIntWord : Integrable (fun p => (regularityCoefficientWord parabolicJointVec w f p)^2) volume :=
    (hWord.1.pow 2).continuous.integrable_of_hasCompactSupport (compact_square hWord.2.1)
  have hIntJet : IntegrableOn
      (valueSquare (jetValue (fun i => (Yau.realVec i,0)) U (jointJetDepth w))) (tsupport χ) := by
    have hV : ContDiff ℝ ∞ (valueSquare (jetValue (fun i => (Yau.realVec i,0)) U (jointJetDepth w))) :=
      ContDiff.sum fun c _ => (jetValue_contDiff _ hU _ c).pow 2
    exact hV.continuous.continuousOn.integrableOn_compact hcχ
  have hPoint : ∀ p ∈ tsupport χ,
      (regularityCoefficientWord parabolicJointVec w f p)^2 ≤
        B^2 * valueSquare (jetValue (fun i => (Yau.realVec i,0)) U (jointJetDepth w)) p := by
    intro p hp
    have hActual := wordJetCLM_actual q e1 e0 hQ U hq hcq he1 hce1 he0 hce0 hχ hU hPDE r w (hχQ hp)
    change _ = _ at hActual
    change (regularityCoefficientWord parabolicJointVec w (fun p => χ p * U p r) p)^2 ≤ _
    rw [hActual]
    have hOp := (wordJetCLM q e1 e0 χ r w p).le_opNorm
      (jetValue (fun i => (Yau.realVec i,0)) U (jointJetDepth w) p)
    have hOpB := hOp.trans (mul_le_mul_of_nonneg_right (hBound p hp) (norm_nonneg _))
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hOpB 2
    have hPi := pi_norm_sq_le_sum_sq (jetValue (fun i => (Yau.realVec i,0)) U (jointJetDepth w) p)
    simp only [Real.norm_eq_abs, sq_abs, mul_pow] at hsq
    exact hsq.trans (mul_le_mul_of_nonneg_left hPi (sq_nonneg B))
  have hLocal : (∫ p in tsupport χ, (regularityCoefficientWord parabolicJointVec w f p)^2) ≤
      B^2 * ∫ p in tsupport χ,
        valueSquare (jetValue (fun i => (Yau.realVec i,0)) U (jointJetDepth w)) p := by
    have h := setIntegral_mono_on hIntWord.integrableOn (hIntJet.const_mul (B^2))
      (isClosed_tsupport χ).measurableSet hPoint
    simpa only [integral_const_mul] using h
  have hEq : (∫ p in tsupport χ, (regularityCoefficientWord parabolicJointVec w f p)^2) =
      ∫ p, (regularityCoefficientWord parabolicJointVec w f p)^2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    rw [image_eq_zero_of_notMem_tsupport (fun h => hp (hSupport h))]
    norm_num
  rw [hEq] at hLocal
  have hEnergyU := hEnergy U hU hPDE hUI
  have hTotal := hLocal.trans (mul_le_mul_of_nonneg_left hEnergyU (sq_nonneg B))
  have hNonneg : 0 ≤ ∫ p in Q, valueSquare U p :=
    integral_nonneg (fun p => valueSquare_nonneg U p)
  change (∫ p, (regularityCoefficientWord parabolicJointVec w f p)^2) ≤ _
  nlinarith

end Yau.NodeProofs.P06Aux.CylinderReg

import Yau.Proofs.P06CylinderRegularityJointEnergy
import Yau.Proofs.P06CylinderRegularityCoordinateWords

/-! The actual interior L²-to-full-joint-Fréchet estimate. All constants
precede the smooth solution and depend only on coefficients and buffers. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem exists_joint_jet_constant {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (e1 : α → α → Yau.RIdx n → Point n → ℝ) (e0 : α → α → Point n → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hcq : ∀ i j, HasCompactSupport (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (hce1 : ∀ r c i, HasCompactSupport (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c)) (hce0 : ∀ r c, HasCompactSupport (e0 r c))
    {Q K : Set (Point n)} (hQ : IsOpen Q) (hK : IsCompact K) (hKQ : K ⊆ Q)
    (lam upper A : ℝ) (hlam : 0 < lam) (hA : 0 ≤ A)
    (hEll : Elliptic Q (heatPrincipal q) lam upper)
    (ha : ∀ p ∈ Q, ∀ i j, |heatPrincipal q p i j| ≤ A) (r : α) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : Point n → α → ℝ,
      (∀ r, ContDiff ℝ ∞ (fun p => U p r)) → heatEquation q e1 e0 Q U →
      IntegrableOn (valueSquare U) Q →
      ∀ p ∈ K, ‖iteratedFDeriv ℝ m (fun p => U p r) p‖^2 ≤
        C * ∫ p in Q, valueSquare U p := by
  classical
  let D := Fintype.card (ParabolicJointIdx n)
  let β := (Fin m → Fin D) × Finset (Fin D)
  let e := parabolicCoordinateEquiv n
  obtain ⟨χ,hχ,hχNear⟩ := exists_test_eq_one_near_compact hQ hK hKQ
  obtain ⟨c,hc,hmap⟩ := parabolicCoordinateEquiv_map_volume n
  have hExists (a : β) : ∃ C : ℝ, 0 < C ∧ ∀ U : Point n → α → ℝ,
      (∀ r, ContDiff ℝ ∞ (fun p => U p r)) → heatEquation q e1 e0 Q U →
      IntegrableOn (valueSquare U) Q →
      (∫ p, (regularityCoefficientWord parabolicJointVec
        ((a.2.sort (· ≤ ·) ++ List.ofFn a.1).map (parabolicJointIndexEquiv n).symm)
        (fun p => χ p * U p r) p)^2) ≤ C * ∫ p in Q, valueSquare U p :=
    exists_joint_word_energy_constant q e1 e0 hq hcq he1 hce1 he0 hce0 hQ χ hχ.1 hχ.2.1 hχ.2.2
      lam upper A hlam hA hEll ha r _
  choose C hC hEnergy using hExists
  let S : ℝ := ∑ w : Fin m → Fin D, ∑ s : Finset (Fin D), C (w,s)
  have hS : 0 ≤ S := Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun s _ => (hC (w,s)).le
  let F : ℝ := ‖e.toContinuousLinearMap‖^(2*m) * (Fintype.card (Fin m → Fin D) : ℝ)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  refine ⟨1+F/c*S,by positivity,?_⟩
  intro U hU hPDE hUI p hp
  let f : Point n → ℝ := fun p => χ p * U p r
  have hf : ContDiff ℝ ∞ f := hχ.1.mul (hU r)
  have hcf : HasCompactSupport f := hχ.2.1.mul_right
  have hSob := iteratedFDeriv_sq_le_coordinate_mixed_energy (m := m) e hf hcf p
  have hTerm (w : Fin m → Fin D) (s : Finset (Fin D)) :
      c * (∫ x, (coordinateWordDerivative (f ∘ e.symm) (s.sort (· ≤ ·) ++ List.ofFn w) x)^2) ≤
        C (w,s) * ∫ p in Q, valueSquare U p := by
    have hT := parabolicCoordinateEquiv_integral hc hmap (fun p =>
      (regularityCoefficientWord parabolicJointVec
        ((s.sort (· ≤ ·) ++ List.ofFn w).map (parabolicJointIndexEquiv n).symm) f p)^2)
    have hE := hEnergy (w,s) U hU hPDE hUI
    simpa only [coordinateWordDerivative_parabolic hf, Function.comp_apply, f, e] using hT.symm.trans_le hE
  have hSum := Finset.sum_le_sum (s := Finset.univ) (fun w _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun s _ => hTerm w s))
  simp only [← Finset.mul_sum, ← Finset.sum_mul] at hSum
  have hDiv : (∑ w : Fin m → Fin D, ∑ s : Finset (Fin D),
      ∫ x, (coordinateWordDerivative (f ∘ e.symm) (s.sort (· ≤ ·) ++ List.ofFn w) x)^2) ≤
        S * (∫ p in Q, valueSquare U p) / c := by
    apply (le_div_iff₀ hc).mpr
    dsimp only [S]
    nlinarith only [hSum]
  have hBound : ‖iteratedFDeriv ℝ m f p‖^2 ≤ F/c*S * ∫ p in Q, valueSquare U p := by
    calc
      _ ≤ F * (∑ w : Fin m → Fin D, ∑ s : Finset (Fin D),
          ∫ x, (coordinateWordDerivative (f ∘ e.symm) (s.sort (· ≤ ·) ++ List.ofFn w) x)^2) := by
        simpa only [F, mul_assoc, e, D] using hSob
      _ ≤ F * (S * (∫ p in Q, valueSquare U p) / c) := mul_le_mul_of_nonneg_left hDiv hF
      _ = _ := by ring
  have hGerm : f =ᶠ[𝓝 p] (fun p => U p r) := cutoff_eq_germ (hχNear p hp)
  have hJet : iteratedFDeriv ℝ m f p = iteratedFDeriv ℝ m (fun p => U p r) p :=
    (hGerm.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds
  rw [hJet] at hBound
  have hNonneg : 0 ≤ ∫ p in Q, valueSquare U p := integral_nonneg fun p => valueSquare_nonneg U p
  nlinarith

end Yau.NodeProofs.P06Aux.CylinderReg

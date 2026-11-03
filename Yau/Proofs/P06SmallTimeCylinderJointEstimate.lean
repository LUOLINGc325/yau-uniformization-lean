import Yau.Proofs.P06SmallTimeCylinderCutoffEnergy

/-! The literal full joint Fréchet estimate has the explicit small-time
power 6*(m+2n+1), before choosing the time or the actual solution. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.SmallTimeCylinder
open Yau.Parabolic Yau.LeafProofs.L16Aux CylinderReg
variable {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]

theorem exists_small_time_joint_jet_constant
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
    (r : α) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℝ) (hτ : 0 < τ), τ ≤ 1 →
      ∀ U : Point n → α → ℝ,
      (∀ r, ContDiff ℝ ∞ (fun p => U p r)) →
      heatEquation q e1 e0 (timeScale τ hτ.ne' '' Q) U →
      IntegrableOn (valueSquare U) (timeScale τ hτ.ne' '' Q) →
      ∀ p ∈ timeScale τ hτ.ne' '' K,
      ‖iteratedFDeriv ℝ m (fun p => U p r) p‖ ^ 2 ≤
        (C / τ ^ (6 * (m + Fintype.card (ParabolicJointIdx n)))) *
          ∫ p in timeScale τ hτ.ne' '' Q, valueSquare U p := by
  classical
  let D := Fintype.card (ParabolicJointIdx n)
  let J := m + D
  let β := (Fin m → Fin D) × Finset (Fin D)
  let e := parabolicCoordinateEquiv n
  obtain ⟨χ, hχ, hχNear⟩ := exists_test_eq_one_near_compact hQ hK hKQ
  obtain ⟨c, hc, hmap⟩ := parabolicCoordinateEquiv_map_volume n
  have hLength (a : β) :
      ((a.2.sort (· ≤ ·) ++ List.ofFn a.1).map (parabolicJointIndexEquiv n).symm).length ≤ J := by
    simp only [List.length_map, List.length_append, Finset.length_sort, List.length_ofFn]
    have hs := Finset.card_le_univ a.2
    simp only [Fintype.card_fin] at hs
    dsimp only [J]
    omega
  have hExists (a : β) := exists_small_time_cutoff_word_energy_constant q e1 e0 hq hcq
    he1 hce1 he0 hce0 hQ χ hχ.1 hχ.2.1 hχ.2.2 lam upper A hlam hA hEll ha r
      ((a.2.sort (· ≤ ·) ++ List.ofFn a.1).map (parabolicJointIndexEquiv n).symm) J (hLength a)
  choose C hC hEnergy using hExists
  let S : ℝ := ∑ w : Fin m → Fin D, ∑ s : Finset (Fin D), C (w,s)
  have hS : 0 ≤ S := Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun s _ => (hC (w,s)).le
  let F : ℝ := ‖e.toContinuousLinearMap‖ ^ (2 * m) * (Fintype.card (Fin m → Fin D) : ℝ)
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  refine ⟨1 + F / c * S, by positivity, ?_⟩
  intro τ hτ hτ1 U hU hPDE hUI p hp
  let χτ := rescaleProfile τ hτ.ne' χ
  let f : Point n → ℝ := fun p => χτ p * U p r
  have hχτ : ContDiff ℝ ∞ χτ := rescaleProfile_contDiff τ hτ.ne' hχ.1
  have hcχτ : HasCompactSupport χτ := rescaleProfile_compact τ hτ.ne' hχ.2.1
  have hf : ContDiff ℝ ∞ f := hχτ.mul (hU r)
  have hcf : HasCompactSupport f := hcχτ.mul_right
  have hSob := iteratedFDeriv_sq_le_coordinate_mixed_energy (m := m) e hf hcf p
  have hTerm (w : Fin m → Fin D) (s : Finset (Fin D)) :
      c * (∫ x, (coordinateWordDerivative (f ∘ e.symm) (s.sort (· ≤ ·) ++ List.ofFn w) x) ^ 2) ≤
        (C (w,s) / τ ^ (6 * J)) * ∫ p in timeScale τ hτ.ne' '' Q, valueSquare U p := by
    have hT := parabolicCoordinateEquiv_integral hc hmap (fun p =>
      (regularityCoefficientWord parabolicJointVec
        ((s.sort (· ≤ ·) ++ List.ofFn w).map (parabolicJointIndexEquiv n).symm) f p) ^ 2)
    have hE := hEnergy (w,s) τ hτ hτ1 U hU hPDE hUI
    simpa only [coordinateWordDerivative_parabolic hf, Function.comp_apply, f, χτ, e] using
      hT.symm.trans_le hE
  have hSum := Finset.sum_le_sum (s := Finset.univ) (fun w _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun s _ => hTerm w s))
  simp only [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_div] at hSum
  have hDiv : (∑ w : Fin m → Fin D, ∑ s : Finset (Fin D),
      ∫ x, (coordinateWordDerivative (f ∘ e.symm) (s.sort (· ≤ ·) ++ List.ofFn w) x) ^ 2) ≤
        ((S / τ ^ (6 * J)) * ∫ p in timeScale τ hτ.ne' '' Q, valueSquare U p) / c := by
    apply (le_div_iff₀ hc).mpr
    dsimp only [S]
    nlinarith only [hSum]
  have hBound : ‖iteratedFDeriv ℝ m f p‖ ^ 2 ≤
      ((F / c * S) / τ ^ (6 * J)) * ∫ p in timeScale τ hτ.ne' '' Q, valueSquare U p := by
    calc
      _ ≤ F * (∑ w : Fin m → Fin D, ∑ s : Finset (Fin D),
          ∫ x, (coordinateWordDerivative (f ∘ e.symm) (s.sort (· ≤ ·) ++ List.ofFn w) x) ^ 2) := by
        simpa only [F, mul_assoc, e, D] using hSob
      _ ≤ F * (((S / τ ^ (6 * J)) * ∫ p in timeScale τ hτ.ne' '' Q, valueSquare U p) / c) :=
        mul_le_mul_of_nonneg_left hDiv hF
      _ = _ := by ring
  have hOne : χτ =ᶠ[𝓝 p] (fun _ => 1) := by
    rcases hp with ⟨p, hp, rfl⟩
    exact rescaleProfile_germ τ hτ.ne' (hχNear p hp)
  have hGerm : f =ᶠ[𝓝 p] (fun p => U p r) := cutoff_eq_germ hOne
  have hJet := (hGerm.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds
  rw [hJet] at hBound
  have hNonneg : 0 ≤ ∫ p in timeScale τ hτ.ne' '' Q, valueSquare U p :=
    integral_nonneg (fun p => valueSquare_nonneg U p)
  exact hBound.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (by linarith) (pow_nonneg hτ.le _)) hNonneg)

end Yau.NodeProofs.P06Aux.SmallTimeCylinder

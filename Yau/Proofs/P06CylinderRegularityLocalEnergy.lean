import Yau.Proofs.P06CylinderRegularityLocalization

/-! The local L²-to-gradient estimate for actual smooth solutions. All
compact extension, global residual, and finite coupling hypotheses are
discharged in its proof. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux

theorem exists_local_system_gradient_constant (n : ℕ) (α : Type*) [Fintype α]
    (lam upper A D B M : ℝ) (hlam : 0 < lam)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hB : 0 ≤ B) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : Set (Point n)) (a : Point n → Mat n)
      (d : α → α → Yau.RIdx n → Point n → ℝ)
      (e : α → α → Point n → ℝ) (η ζ : Point n → ℝ)
      (U : Point n → α → ℝ),
    IsOpen Q → Elliptic Q a lam upper →
    (∀ p ∈ Q, ∀ i j, |a p i j| ≤ A) →
    (∀ i j, ContDiff ℝ ∞ (fun p => a p i j)) →
    (∀ r c i, ContDiff ℝ ∞ (d r c i)) →
    (∀ r c, ContDiff ℝ ∞ (e r c)) →
    (∀ r c i p, |d r c i p| ≤ D) → (∀ r c p, |e r c p| ≤ B) →
    Test Q η → Test Q ζ → (∀ p, |η p| ≤ 1) → (∀ p, |ζ p| ≤ 1) →
    (∀ p ∈ tsupport η, ζ =ᶠ[𝓝 p] (fun _ => 1)) →
    (∀ p, |fderiv ℝ η p (0,1)| ≤ M) →
    (∀ p i, |fderiv ℝ η p (Yau.realVec i,0)| ≤ M) →
    (∀ r, ContDiffOn ℝ ∞ (fun p => U p r) Q) →
    IntegrableOn (valueSquare U) Q →
    (∀ p ∈ Q, ∀ r, fderiv ℝ (fun q => U q r) p (0,1) =
      (∑ i, fderiv ℝ (fun q => systemFlux a d U r q i) p (Yau.realVec i,0)) +
        valueSource e U r p) →
    (∫ p, η p^2 * ∑ r, ∑ i, (spatialGradient (fun q => U q r) p i)^2) ≤
      C * ∫ p in Q, valueSquare U p := by
  classical
  obtain ⟨C,hC,hEst⟩ := exists_system_gradient_constant n α lam upper A D B M
    hlam hA hD hB hM
  refine ⟨C,hC,?_⟩
  intro Q a d e η ζ U hQ hEll ha haS hdS heS hd he hη hζ hηB hζB hζone
    hTime hSpace hU hUI hPDE
  let V : Point n → α → ℝ := fun p r => ζ p * U p r
  have hV (r : α) : ContDiff ℝ ∞ (fun p => V p r) :=
    (cutoff_contDiff hQ hζ.1 hζ.2.1 hζ.2.2 (hU r)).1
  have hcV (r : α) : HasCompactSupport (fun p => V p r) :=
    (cutoff_contDiff hQ hζ.1 hζ.2.1 hζ.2.2 (hU r)).2
  have hVeq := cutoff_system_equation hη.2.2 hζone hPDE
  have hBound := hEst Q a d e η V hEll ha haS hdS heS hd he hη hηB hTime hSpace hV hcV hVeq
  have hIntV := valueSquare_integrable hV hcV
  have hValue := cutoff_valueSquare_bound hQ.measurableSet hζ.2.2 hζB hUI hIntV
  have hSame : (fun p => η p^2 * ∑ r, ∑ i, (spatialGradient (fun q => V q r) p i)^2) =
      fun p => η p^2 * ∑ r, ∑ i, (spatialGradient (fun q => U q r) p i)^2 := by
    funext p
    by_cases hp : p ∈ tsupport η
    · congr 1
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro i _
      have hG : fderiv ℝ (fun q => ζ q * U q r) p = fderiv ℝ (fun q => U q r) p :=
        (cutoff_eq_germ (f := fun q => U q r) (hζone p hp)).fderiv.eq_of_nhds
      dsimp only [V, spatialGradient]
      rw [hG]
    · simp only [image_eq_zero_of_notMem_tsupport hp, zero_pow (by decide : 2 ≠ 0), zero_mul]
  rw [hSame] at hBound
  exact hBound.trans (mul_le_mul_of_nonneg_left hValue hC.le)

end Yau.NodeProofs.P06Aux.CylinderReg

import Yau.Proofs.P06CylinderRegularityLocalEnergy
import Yau.Proofs.P06CylinderRegularitySpatialEnergy

/-! A fixed numerical Caccioppoli constant yields an explicit inverse-square
small-time cost by normalizing the test, rather than changing its derivative
bound after the constant has been chosen. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.SmallTimeCylinder
open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux CylinderReg
variable {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]

theorem scaled_test {Q : Set (Point n)} {η : Point n → ℝ}
    (hη : Test Q η) (a : ℝ) : Test Q (fun p => a * η p) := by
  refine ⟨contDiff_const.mul hη.1, hη.2.1.mul_left, ?_⟩
  have hs : tsupport (fun p => a * η p) ⊆ tsupport η := tsupport_mul_subset_right
  exact hs.trans hη.2.2

theorem normalized_test_bounds {Q : Set (Point n)} {η : Point n → ℝ}
    (hη : Test Q η) (hηB : ∀ p, |η p| ≤ 1)
    {M τ : ℝ} (hM : 0 ≤ M) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hTime : ∀ p, |fderiv ℝ η p (0,1)| ≤ M / τ)
    (hSpace : ∀ p i, |fderiv ℝ η p (Yau.realVec i,0)| ≤ M / τ) :
    let ηhat := fun p => (τ / (M + 1)) * η p
    (∀ p, |ηhat p| ≤ 1) ∧
      (∀ p, |fderiv ℝ ηhat p (0,1)| ≤ 1) ∧
      ∀ p i, |fderiv ℝ ηhat p (Yau.realVec i,0)| ≤ 1 := by
  dsimp only
  have hden : 0 < M + 1 := by linarith
  have ha : 0 ≤ τ / (M + 1) := div_nonneg hτ.le hden.le
  have ha1 : τ / (M + 1) ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hderiv (p : Point n) (v : Point n)
      (hv : |fderiv ℝ η p v| ≤ M / τ) :
      |fderiv ℝ (fun p => τ / (M + 1) * η p) p v| ≤ 1 := by
    rw [fderiv_const_mul (hη.1.differentiable (by simp) p)]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ha]
    calc
      _ ≤ (τ / (M + 1)) * (M / τ) := mul_le_mul_of_nonneg_left hv ha
      _ = M / (M + 1) := by field_simp [hτ.ne']
      _ ≤ 1 := (div_le_one hden).mpr (by linarith)
  refine ⟨?_, fun p => hderiv p (0,1) (hTime p), fun p i => hderiv p _ (hSpace p i)⟩
  intro p
  rw [abs_mul, abs_of_nonneg ha]
  exact (mul_le_mul_of_nonneg_left (hηB p) ha).trans (by simpa only [mul_one] using ha1)

theorem inner_gradient_energy_plateau_le {Q K : Set (Point n)}
    (hQ : IsOpen Q) (hK : MeasurableSet K) {η : Point n → ℝ} (hη : Test Q η)
    (a : ℝ) (hηa : ∀ p ∈ K, η p = a) {U : Point n → α → ℝ}
    (hU : ∀ r, ContDiffOn ℝ ∞ (fun p => U p r) Q) :
    a ^ 2 * (∫ p in K, gradientSquare U p) ≤
      ∫ p, η p ^ 2 * gradientSquare U p := by
  have hInt := weighted_gradient_integrable hQ hη hU
  have hEq : a ^ 2 * (∫ p in K, gradientSquare U p) =
      ∫ p in K, η p ^ 2 * gradientSquare U p := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun hK (fun p hp => by rw [hηa p hp])
  rw [hEq]
  exact setIntegral_le_integral hInt (Eventually.of_forall
    (fun p => mul_nonneg (sq_nonneg _) (gradientSquare_nonneg U p)))

/-- The constant is selected with the fixed numerical test-derivative bound
one, before the small time, the tests, or the actual local smooth solution. -/
theorem exists_small_time_local_gradient_constant (n : ℕ) (α : Type*) [Fintype α] [DecidableEq α]
    (lam upper A D B M : ℝ) (hlam : 0 < lam)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hB : 0 ≤ B) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
    ∀ (Q K : Set (Point n)) (a : Point n → Mat n)
      (d : α → α → Yau.RIdx n → Point n → ℝ)
      (e : α → α → Point n → ℝ) (η ζ : Point n → ℝ)
      (U : Point n → α → ℝ),
    IsOpen Q → MeasurableSet K → Elliptic Q a lam upper →
    (∀ p ∈ Q, ∀ i j, |a p i j| ≤ A) →
    (∀ i j, ContDiff ℝ ∞ (fun p => a p i j)) →
    (∀ r c i, ContDiff ℝ ∞ (d r c i)) →
    (∀ r c, ContDiff ℝ ∞ (e r c)) →
    (∀ r c i p, |d r c i p| ≤ D) → (∀ r c p, |e r c p| ≤ B) →
    Test Q η → Test Q ζ → (∀ p, |η p| ≤ 1) → (∀ p, |ζ p| ≤ 1) →
    (∀ p ∈ tsupport η, ζ =ᶠ[𝓝 p] (fun _ => 1)) →
    (∀ p ∈ K, η p = 1) →
    (∀ p, |fderiv ℝ η p (0,1)| ≤ M / τ) →
    (∀ p i, |fderiv ℝ η p (Yau.realVec i,0)| ≤ M / τ) →
    (∀ r, ContDiffOn ℝ ∞ (fun p => U p r) Q) →
    IntegrableOn (valueSquare U) Q →
    (∀ p ∈ Q, ∀ r, fderiv ℝ (fun q => U q r) p (0,1) =
      (∑ i, fderiv ℝ (fun q => systemFlux a d U r q i) p (Yau.realVec i,0)) +
        valueSource e U r p) →
    (∫ p in K, gradientSquare U p) ≤
      (C / τ ^ 2) * ∫ p in Q, valueSquare U p := by
  obtain ⟨C0, hC0, hEst⟩ := exists_local_system_gradient_constant n α
    lam upper A D B 1 hlam hA hD hB zero_le_one
  refine ⟨C0 * (M + 1) ^ 2, mul_pos hC0 (sq_pos_of_pos (by linarith)), ?_⟩
  intro τ hτ hτ1 Q K a d e η ζ U hQ hK hEll ha haS hdS heS hd he
    hη hζ hηB hζB hζNear hηOne hTime hSpace hU hUI hPDE
  let ηhat := fun p => τ / (M + 1) * η p
  have hηhat : Test Q ηhat := scaled_test hη _
  have hηhatBounds := normalized_test_bounds hη hηB hM hτ hτ1 hTime hSpace
  have hNear : ∀ p ∈ tsupport ηhat, ζ =ᶠ[𝓝 p] (fun _ => 1) := by
    intro p hp
    have hs : tsupport ηhat ⊆ tsupport η := tsupport_mul_subset_right
    exact hζNear p (hs hp)
  have hGrad := hEst Q a d e ηhat ζ U hQ hEll ha haS hdS heS hd he
    hηhat hζ hηhatBounds.1 hζB hNear hηhatBounds.2.1 hηhatBounds.2.2 hU hUI hPDE
  have hInner := inner_gradient_energy_plateau_le hQ hK hηhat (τ / (M + 1))
    (fun p hp => by dsimp only [ηhat]; rw [hηOne p hp, mul_one]) hU
  have hCombined := hInner.trans hGrad
  have hden : M + 1 ≠ 0 := ne_of_gt (by linarith : 0 < M + 1)
  calc
    _ = ((M + 1) ^ 2 / τ ^ 2) *
        ((τ / (M + 1)) ^ 2 * (∫ p in K, gradientSquare U p)) := by
      field_simp [hden, hτ.ne']
      <;> ring
    _ ≤ ((M + 1) ^ 2 / τ ^ 2) * (C0 * ∫ p in Q, valueSquare U p) :=
      mul_le_mul_of_nonneg_left hCombined (by positivity)
    _ = _ := by ring

end Yau.NodeProofs.P06Aux.SmallTimeCylinder

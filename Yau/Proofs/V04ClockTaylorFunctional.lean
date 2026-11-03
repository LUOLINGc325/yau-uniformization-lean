import Yau.Proofs.V04ClockTaylorBoundaryEstimate
import Yau.Proofs.V04ClockTaylorCenter

/-! Actual admissible backward clocks and Taylor's theorem for the same
whole penalized functional. Its remainder may depend on a fixed energy cap. -/
open Set
open scoped Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof.ClockTaylorAux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem logBackwardClock_admissible {d : VariationData X q} {k : ClockData X} {j a : ℕ}
    {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) {Γ : ℂ → ℂ}
    (hΓ : ClockLift d k j a F Γ)
    (hβ : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, 0 ≤ 1 + (Γ z).re)
    {u : ℝ} (hu : u ≤ 0)
    (hc : InCotangentTimeChart d.chart (F.f 0) (F.s * Real.exp u) (centerCylinder d)) :
    AdmissibleVariationDisc d j (logBackwardClock F Γ u) := by
  obtain ⟨hf, hw, hw0, hs, hsT, _, ht, hb, he⟩ := hF
  have hs' := mul_pos hs (Real.exp_pos u)
  have hle := mul_le_of_le_one_right hs.le (Real.exp_le_one_iff.mpr hu)
  have hnew := backwardClock_smooth_center hw hw0 hΓ.1 hΓ.2.1 (F.s * Real.exp u)
  have htime := backwardClock_discTime_le F Γ hs hs' hle hβ
  exact ⟨hf, hnew.1, hnew.2, hs', hle.trans_lt hsT, hc,
    fun ζ hζ => (htime ζ hζ).trans_lt (ht ζ hζ), hb, backwardClock_energy_ne_top he hnew.1⟩

theorem whole_functional_backward_taylor {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) (j a : ℕ)
    {Kc : Set (CotangentCoord n × ℝ)} (hKc : IsCompact Kc)
    (hKcO : Kc ⊆ interior (centerCylinder d)) {C M E₀ ε : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hE₀ : 0 ≤ E₀) (hε : 0 ≤ ε) :
    ∃ r R : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 ≤ R ∧ ∀ F : VariationDisc X,
      AdmissibleVariationDisc d j F → InCotangentTimeChart d.chart (F.f 0) F.s Kc →
      boundaryCost d j F ≤ M → (variationEnergy d j F).toReal ≤ E₀ →
      ∀ Γ : ℂ → ℂ, ClockLift d k j a F Γ →
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, 0 ≤ 1 + (Γ z).re) →
      (∀ θ, clockWeight d k j a F θ ≤ C) →
      boundaryDSq (fun θ (_ : Unit) => Γ (circlePoint θ)) ≤ ENNReal.ofReal C * variationEnergy d j F →
      ∀ u ∈ Icc (-r) 0,
        AdmissibleVariationDisc d j (logBackwardClock F Γ u) ∧
        |penalizedFunctional d j ε (logBackwardClock F Γ u) - penalizedFunctional d j ε F -
          u * (F.s * (clockBoundaryCost d k j a F - deriv (d.test (F.f 0)) F.s) +
            ε * clockEnergyLinear F Γ)| ≤ R * u ^ 2 := by
  obtain ⟨R₁, hR₁, hbc⟩ := fixed_index_boundaryCost_taylor hd hk j a hC hM
  obtain ⟨r, R₂, hr, hr1, hR₂, htest⟩ := compact_center_test_taylor hd hKc hKcO
  let R := R₁ + R₂ + ε * (Real.pi / 2) * C * E₀
  refine ⟨r, R, hr, hr1, by dsimp [R]; positivity, ?_⟩
  intro F hF hc hFM hFE Γ hΓ hβ hγ hΓD u hu
  have hu1 : u ∈ Icc (-1) 0 := ⟨(neg_le_neg hr1).trans hu.1, hu.2⟩
  have ht := htest F hc hF.2.2.2.1 hF.2.2.2.2.1.le u hu
  have hadm := logBackwardClock_admissible hF hΓ hβ hu.2 ⟨ht.1.1, interior_subset ht.1.2⟩
  refine ⟨hadm, ?_⟩
  have hb := hbc F hF hFM Γ hΓ hβ hγ u hu1
  have hD : (boundaryDSq (fun θ (_ : Unit) => Γ (circlePoint θ))).toReal ≤ C * E₀ := by
    have hh := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hF.2.2.2.2.2.2.2.2) hΓD
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hFE hC)
  have he : |ε * ((variationEnergy d j (logBackwardClock F Γ u)).toReal -
      (variationEnergy d j F).toReal - u * clockEnergyLinear F Γ)| ≤
        (ε * (Real.pi / 2) * C * E₀) * u ^ 2 := by
    rw [logBackwardClock_energy_difference hF hΓ.1 u]
    have hid : ε * (u * clockEnergyLinear F Γ + (Real.pi / 2) * u ^ 2 *
        (boundaryDSq (fun θ (_ : Unit) => Γ (circlePoint θ))).toReal - u * clockEnergyLinear F Γ) =
        (ε * (Real.pi / 2) * u ^ 2) * (boundaryDSq (fun θ (_ : Unit) => Γ (circlePoint θ))).toReal := by ring
    rw [hid, abs_of_nonneg (by positivity)]
    exact (mul_le_mul_of_nonneg_left hD (by positivity)).trans_eq (by ring)
  have heq : penalizedFunctional d j ε (logBackwardClock F Γ u) - penalizedFunctional d j ε F -
      u * (F.s * (clockBoundaryCost d k j a F - deriv (d.test (F.f 0)) F.s) + ε * clockEnergyLinear F Γ) =
      (boundaryCost d j (logBackwardClock F Γ u) - boundaryCost d j F - u * F.s * clockBoundaryCost d k j a F) -
      (d.test (F.f 0) (F.s * Real.exp u) - d.test (F.f 0) F.s - u * F.s * deriv (d.test (F.f 0)) F.s) +
      ε * ((variationEnergy d j (logBackwardClock F Γ u)).toReal - (variationEnergy d j F).toReal -
        u * clockEnergyLinear F Γ) := by
    unfold penalizedFunctional
    change _ + _ - d.test (F.f 0) (F.s * Real.exp u) - (_ + _ - _) - _ = _
    ring
  rw [heq]
  calc
    _ ≤ |boundaryCost d j (logBackwardClock F Γ u) - boundaryCost d j F - u * F.s * clockBoundaryCost d k j a F| +
        |d.test (F.f 0) (F.s * Real.exp u) - d.test (F.f 0) F.s - u * F.s * deriv (d.test (F.f 0)) F.s| +
        |ε * ((variationEnergy d j (logBackwardClock F Γ u)).toReal - (variationEnergy d j F).toReal -
          u * clockEnergyLinear F Γ)| := (abs_add_le _ _).trans (add_le_add (abs_sub _ _) (le_refl _))
    _ ≤ R₁ * u ^ 2 + R₂ * u ^ 2 + (ε * (Real.pi / 2) * C * E₀) * u ^ 2 :=
      add_le_add (add_le_add hb ht.2) he
    _ = R * u ^ 2 := by dsimp [R]; ring

end Yau.Blueprint.V04Proof.ClockTaylorAux

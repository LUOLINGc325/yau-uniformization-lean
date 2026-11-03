import Yau.LeafProofs.L21LeviWeightError

/-! Uniform corrected Levi positivity for arbitrary smooth small graph
coefficients. The constants are chosen before the domain and coefficients. -/

open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

theorem exists_uniform_corrected_levi (n : ℕ) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
    ∀ (O : Set (X n)) (A : X n → Matrix (Fin n) (Fin n) ℂ),
      IsOpen O → MatrixSmoothOn A O → JetBound 1 ε A O → JetBound 2 1 A O →
      ∃ c d : Fin n → Fin n → Fin n → X n → ℂ,
        (∀ i j k, ContDiffOn ℝ ∞ (c i j k) O ∧ ContDiffOn ℝ ∞ (d i j k) O) ∧
        (∀ x ∈ O, ∀ i j k, ‖c i j k x‖ ≤ C * mixedFrameDerivativeSize A x ∧
          ‖d i j k x‖ ≤ C * mixedFrameDerivativeSize A x) ∧
        (∀ x ∈ O, ∀ i j k, ‖fderiv ℝ (c i j k) x‖ ≤ C ∧ ‖fderiv ℝ (d i j k) x‖ ≤ C) ∧
        (∀ x ∈ O, ∀ i j k, star (d j i k x) = -c i j k x) ∧
        (∀ f : X n → ℂ, ContDiffOn ℝ ∞ f O → ∀ x ∈ O, ∀ i j,
          dbarA A i (conjugateD A j f) x - conjugateD A j (dbarA A i f) x =
            ∑ k, (c i j k x * dbarA A k f x + d i j k x * conjugateD A k f x)) ∧
        ∀ K : ℝ, 0 ≤ K → ∀ x ∈ O, x ∈ Metric.ball (0 : X n) 1 → ∀ ξ : Fin n → ℂ,
          (K / 2) * (rho x)⁻¹ ^ 2 * (∑ i, ‖ξ i‖ ^ 2) ≤
            (∑ i, ∑ j, star (ξ i) * correctedLevi A (boundaryWeight K) d i j x * ξ j).re := by
  obtain ⟨ε0, C, hε0, hC, hFrame⟩ := exists_mixed_frame_coefficients n
  let CE : ℝ := 2 * (realDimension n : ℝ) + 2 * (n : ℝ) * (C * (n : ℝ) ^ 2)
  let L : ℝ := (n : ℝ) * (realDimension n : ℝ) * CE
  have hCE : 0 ≤ CE := by dsimp [CE]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let ε : ℝ := min ε0 (1 / (4 * (L + 1)))
  have hε : 0 < ε := lt_min hε0 (by positivity)
  have hε0le : ε ≤ ε0 := min_le_left _ _
  have hεL : ε ≤ 1 / (4 * (L + 1)) := min_le_right _ _
  have hmul : ε * (4 * (L + 1)) ≤ 1 := (le_div_iff₀ (by positivity)).mp hεL
  have hsmall : 2 * (n : ℝ) * (realDimension n : ℝ) * CE * ε ≤ 1 / 2 := by
    have hh : 2 * L * ε ≤ 1 / 2 := by nlinarith [hε.le]
    calc
      _ = 2 * L * ε := by dsimp [L]; ring
      _ ≤ _ := hh
  refine ⟨ε, C, hε, hC, ?_⟩
  intro O A hO hA hSmall hJet
  have hSmall0 : JetBound 0 ε0 A O := fun m hm x hx i j =>
    (hSmall m (by omega) x hx i j).trans hε0le
  obtain ⟨c, d, hSmooth, hValues, hDerivatives, hConj, hBracket⟩ := hFrame O A hO hA hSmall0 hJet
  refine ⟨c, d, hSmooth, hValues, hDerivatives, hConj, hBracket, ?_⟩
  intro K hK x hx hxB ξ
  have hDA (i k : Fin n) : ‖fderiv ℝ (fun y => A y i k) x‖ ≤ ε := by
    simpa only [norm_iteratedFDeriv_one] using hSmall 1 le_rfl x hx i k
  have hd (i j k : Fin n) : ‖d i j k x‖ ≤ (C * (n : ℝ) ^ 2) * ε := by
    exact (hValues x hx i j k).2.trans
      ((mul_le_mul_of_nonneg_left (mixedFrameDerivativeSize_le_jet hSmall hx) hC.le).trans_eq (by ring))
  have hE (i j : Fin n) (b : Yau.RIdx n) : ‖leviFirstCoefficient A d i j b x‖ ≤ CE * ε :=
    leviFirstCoefficient_norm_bound hO hA hx (fun r s => (mixedFrame_jet_fderiv hJet hx r s).1)
      hε.le (by positivity) hDA d hd i j b
  exact correctedLevi_boundaryWeight_lower_of_error hO hA d hK hx hxB hε.le hCE hE hsmall ξ

end Yau.LeafProofs.L21Aux

import Yau.Proofs.P08ExhaustionTrace
import Yau.Proofs.P08ExhaustionScaling

/-! Quantitative compact cutoffs are consequences of precisely the frozen
controlled exhaustion, with all constants fixed before the scale. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.P08Aux
open Yau Yau.Blueprint Yau.LeafProofs
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem exists_exhaustion_laplacian_cutoffs (X : KahlerManifold n) (o : Pt X)
    {u : Pt X → ℝ} (hu : ControlledExhaustion X o u) :
    ∃ ρ A : ℝ, 1 ≤ ρ ∧ 0 < A ∧ ∀ L : ℝ, 1 ≤ L →
      ∃ χ : Pt X → ℝ, SmoothFn χ ∧ HasCompactSupport χ ∧
        (∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ x, distFrom X.metric.form o x ≤ L → χ x = 1) ∧
        tsupport χ ⊆ distBall X.metric.form o (ρ * L) ∧
        ∀ x, |laplacian X.metric.form χ x| ≤ A / L ^ 2 := by
  obtain ⟨hs, hproper, hge, C, hC, hdata⟩ := hu
  obtain ⟨B, hB, hB2, hB1⟩ := exists_exhaustionProfile_derivative_bound
  have hC1 : 1 ≤ C := by
    have ho := (hdata o).2.1
    have hoo : distFrom X.metric.form o o = 0 := X.metric.induced_distance_eq_zero.mpr rfl
    rw [hoo, add_zero, mul_one] at ho
    exact (hge o).trans ho
  let ρ : ℝ := 4 * C ^ 2
  let A : ℝ := B * (n + 1)
  have hρ : 1 ≤ ρ := by dsimp only [ρ]; nlinarith
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨ρ, A, hρ, hA, ?_⟩
  intro L hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let a : ℝ := 2 * C * L
  have ha : 0 < a := by dsimp only [a]; positivity
  let χ : Pt X → ℝ := fun x => exhaustionScaledProfile a (u x)
  have hχ : SmoothFn χ := L18Aux.smoothFn_scalar_comp hs _ (exhaustionScaledProfile_contDiff a)
  have hsupport : tsupport χ ⊆ {x | u x ≤ 2 * a} := by
    apply closure_minimal ?_ (isClosed_le (L18Aux.continuous_of_smoothFn hs) continuous_const)
    intro x hx
    by_contra hxu
    have hlarge : 2 ≤ |u x / a| := by
      rw [abs_of_pos (div_pos (lt_trans (by positivity : 0 < 2 * a) (lt_of_not_ge hxu)) ha)]
      exact (le_div_iff₀ ha).mpr (lt_of_not_ge hxu).le
    exact hx (exhaustionProfile_zero hlarge)
  have hcχ : HasCompactSupport χ :=
    (hproper (2 * a)).of_isClosed_subset (isClosed_tsupport χ) hsupport
  refine ⟨χ, hχ, hcχ, ?_, ?_, ?_, ?_⟩
  · intro x
    exact ⟨exhaustionProfile.nonneg, exhaustionProfile.le_one⟩
  · intro x hx
    apply exhaustionProfile_one
    rw [abs_of_pos (div_pos (lt_of_lt_of_le zero_lt_one (hge x)) ha)]
    apply (div_le_one ha).mpr
    have hxup := (hdata x).2.1
    dsimp only [a]
    nlinarith
  · intro x hx
    have hux := hsupport hx
    have hd := (inv_mul_le_iff₀ hC).mp (hdata x).1
    apply (L12Aux.mem_distBall_iff X.metric o x (mul_pos (lt_of_lt_of_le zero_lt_one hρ) hLpos)).mpr
    change distFrom X.metric.form o x < ρ * L
    change u x ≤ 2 * a at hux
    have hmul := mul_le_mul_of_nonneg_left hux hC.le
    dsimp only [a, ρ] at hmul ⊢
    nlinarith
  · intro x
    have hux : 0 < u x := lt_of_lt_of_le zero_lt_one (hge x)
    have hΔ := laplacian_abs_le_of_levi_bounds X.metric.form u x (C / u x)
      (by simpa only [Complex.ofReal_div] using (hdata x).2.2.2.1) (hdata x).2.2.2.2
    have hgrad := (hdata x).2.2.1
    have hgrad0 : 0 ≤ gradNormSq X.metric.form u x := by
      have h := L18Aux.scalarGradientPair_self_nonneg X.metric.form u x
      rw [L18Aux.scalarGradientPair_eq_twice_gradNormSq X.metric.form hs x] at h
      linarith
    have hchain := L18Aux.laplacian_scalar_comp X.metric.form hs (exhaustionScaledProfile a) x
      ((exhaustionScaledProfile_contDiff a).contDiffAt.of_le (by simp))
    rw [exhaustionScaledProfile_deriv, exhaustionScaledProfile_deriv_deriv,
      L18Aux.scalarGradientPair_eq_twice_gradNormSq X.metric.form hs x] at hchain
    have hfirst : |deriv (exhaustionProfile : ℝ → ℝ) (u x / a) / a * laplacian X.metric.form u x| ≤
        B * C * n / a ^ 2 := by
      rw [abs_mul, abs_div, abs_of_pos ha]
      calc
        _ ≤ (B * (u x / a) / a) * ((C / u x) * n) :=
          mul_le_mul (div_le_div_of_nonneg_right (hB1 _ (div_nonneg hux.le ha.le)) ha.le)
            hΔ (abs_nonneg _) (by positivity)
        _ = _ := by field_simp <;> ring
    have hsecond : |deriv (deriv (exhaustionProfile : ℝ → ℝ)) (u x / a) / a ^ 2 *
        gradNormSq X.metric.form u x| ≤ B / a ^ 2 * C ^ 2 := by
      rw [abs_mul, abs_div, abs_of_pos (sq_pos_of_pos ha), abs_of_nonneg hgrad0]
      exact mul_le_mul (div_le_div_of_nonneg_right (hB2 _) (sq_nonneg a)) hgrad hgrad0 (by positivity)
    have hbound : |laplacian X.metric.form χ x| ≤ B * (C * n + C ^ 2) / a ^ 2 := by
      change |laplacian X.metric.form (fun y => exhaustionScaledProfile a (u y)) x| ≤ _
      rw [hchain]
      calc
        _ = |deriv (exhaustionProfile : ℝ → ℝ) (u x / a) / a * laplacian X.metric.form u x +
            deriv (deriv (exhaustionProfile : ℝ → ℝ)) (u x / a) / a ^ 2 * gradNormSq X.metric.form u x| := by congr 1; ring
        _ ≤ _ := (abs_add_le _ _).trans (add_le_add hfirst hsecond)
        _ = _ := by ring
    apply hbound.trans
    calc
      _ ≤ B * C ^ 2 * (n + 1) / a ^ 2 := by
        apply div_le_div_of_nonneg_right ?_ (sq_nonneg a)
        have hCn : C * (n : ℝ) ≤ C ^ 2 * n :=
          mul_le_mul_of_nonneg_right (by nlinarith) (Nat.cast_nonneg n)
        nlinarith
      _ = A / (4 * L ^ 2) := by dsimp only [a, A]; field_simp <;> ring
      _ ≤ A / L ^ 2 := by
        apply div_le_div_of_nonneg_left hA.le (sq_pos_of_pos hLpos)
        nlinarith [sq_nonneg L]

end Yau.NodeProofs.P08Aux

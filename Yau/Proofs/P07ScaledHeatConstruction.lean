import Yau.Proofs.P07HeatScaled
import Yau.Proofs.P07Step
import Yau.Proofs.P07ScaledFamily
import Yau.Proofs.P07ProfilesRadial

/-! The original rough compact-exterior heat theorem produces the actual
scaled smooth cutoffs. The sole geometric input is the separately proved
weak Levi estimate for the fixed radial truncations. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff ComplexOrder
namespace Yau.NodeProofs.P07Aux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux Yau.LeafProofs.L18Aux Yau.LeafProofs.L19Aux
variable {n : ℕ}

theorem scaledCutoffs_of_roughHeat_radialWeak (X : KahlerManifold n) (o : Pt X)
    (μ : MeasureTheory.Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (hrough : LipschitzHessianHeatTarget X) {A : ℝ} (hA : 0 < A)
    (hweak : ∀ L : ℝ, 0 < L → WeakLeviUpper X.metric.form (radialTruncation X.metric o L) (A / L ^ 2)) :
    ∃ (v : ℝ → Pt X → ℝ) (D1 D2 : ℝ), 0 < D1 ∧ 0 < D2 ∧
      ScaledCutoffFamily X.metric o v D1 D2 := by
  classical
  obtain ⟨A1, A2, hA1, hA2, hAd⟩ := radialProfile_derivative_bounds
  let K0 := 4 * A1
  have hK0 : 0 < K0 := by dsimp only [K0]; positivity
  obtain ⟨ε, hε, htime⟩ := exists_uniform_heat_time n hK0
  obtain ⟨B1, B2, hB1, hB2, hBd⟩ := cutoffTransition_derivative_bounds
  let G := 12 * (n : ℝ) / ε
  let W := ((n : ℝ) + 1) * A + 2 * (n : ℝ) / ε
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (complexDimension_pos X.manifold)
  have hG : 0 < G := by dsimp only [G]; positivity
  have hW : 0 < W := by dsimp only [W]; positivity
  let D1 := B1 * Real.sqrt G
  let D2 := B1 * W + 2 * B2 * G
  have hD1 : 0 < D1 := mul_pos hB1 (Real.sqrt_pos.mpr hG)
  have hD2 : 0 < D2 := by dsimp only [D2]; positivity
  have hscale : ∀ L : ℝ, 0 < L → ∃ w : Pt X → ℝ,
      SmoothFn w ∧ ∀ x,
        w x ∈ Icc (0 : ℝ) 1 ∧
        (distFrom X.metric.form o x ≤ L → w =ᶠ[𝓝 x] fun _ => 0) ∧
        (2 * L ≤ distFrom X.metric.form o x → w =ᶠ[𝓝 x] fun _ => 1) ∧
        gradNormSq X.metric.form w x ≤ (D1 / L) ^ 2 ∧
        ∀ z : ComplexVector n, |leviDirection (levi w x) z| ≤
          (D2 / L ^ 2) * leviDirection (gMat X.metric.form x) z := by
    intro L hL
    let f := radialTruncation X.metric o L
    have hLipB : ∀ x y, |f x - f y| ≤ (K0 / L) * inducedDistance X.metric.form x y :=
      radialTruncation_lipschitz_bound X.metric o hA1 hL (fun s => (hAd s).1)
    have hLip : LipschitzForMetric X.metric.form f := ⟨K0 / L, (div_pos hK0 hL).le, hLipB⟩
    obtain ⟨K, hK, hKf⟩ := radialTruncation_compactExterior X.metric o hL
    have hc : Continuous (fun x => f x - 1) := (radialTruncation_continuous X.metric o L).sub continuous_const
    have hcomp : HasCompactSupport (fun x => f x - 1) := by
      apply hK.of_isClosed_subset isClosed_closure
      apply closure_minimal _ hK.isClosed
      intro x hx
      by_contra hxK
      exact hx (sub_eq_zero.mpr (hKf x hxK))
    have hsol := hrough f (A / L ^ 2) hLip ⟨K, 1, hK, hKf⟩ (hweak L hL)
    obtain ⟨U, hU⟩ := hsol.1
    have ht : 0 < ε * L ^ 2 := mul_pos hε (sq_pos_of_pos hL)
    have hU01 (x t) (ht : 0 < t) : U t x ∈ Icc (0 : ℝ) 1 :=
      continuousInitialHeat_unit_range X μ hμ f hc hcomp (radialTruncation_mem X.metric o L) U hU ht x
    have herr (x) : |U (ε * L ^ 2) x - f x| ≤ 1 / 16 := by
      have he := continuousInitialHeat_lipschitz_error X μ hμ f hc hcomp
        (radialTruncation_mem X.metric o L) (div_pos hK0 hL) hLipB U hU ht x
      rwa [htime L hL] at he
    have hder := continuousInitialHeat_scaled_derivatives X f U hU hU01 hA hε hL
      (hsol.2.2 U hU (ε * L ^ 2) ht)
    let u := U (ε * L ^ 2)
    have hu : SmoothFn u := smoothSpaceTime_slice hU.2.1 ht
    let w := fun x => cutoffTransition (u x)
    have hw : SmoothFn w := smoothFn_scalar_comp hu cutoffTransition cutoffTransition_contDiff
    refine ⟨w, hw, ?_⟩
    intro x
    refine ⟨cutoffTransition_mem _, ?_, ?_, ?_, ?_⟩
    · intro hx
      have he := herr x
      have hf0 : f x = 0 := radialTruncation_zero X.metric o hL x hx
      rw [hf0, sub_zero] at he
      exact step_locally_zero (continuous_of_smoothFn hu) ((le_abs_self _).trans he)
    · intro hx
      have he := herr x
      have hf1 : f x = 1 := radialTruncation_one X.metric o hL x hx
      rw [hf1] at he
      apply step_locally_one (continuous_of_smoothFn hu)
      dsimp only [u]
      linarith [neg_abs_le (U (ε * L ^ 2) x - 1)]
    · change gradNormSq X.metric.form (fun y => cutoffTransition (u y)) x ≤ _
      rw [gradNormSq_scalar_comp X.metric.form hu cutoffTransition cutoffTransition_contDiff x]
      have hs : deriv cutoffTransition (u x) ^ 2 ≤ B1 ^ 2 := by
        simpa only [sq_abs] using
          ((sq_le_sq₀ (abs_nonneg (deriv cutoffTransition (u x))) hB1.le).mpr (hBd (u x)).1)
      have hb := mul_le_mul hs (hder.1 x) (gradNormSq_nonnegative X.metric.form hu x) (sq_nonneg B1)
      have he : B1 ^ 2 * (G / L ^ 2) = (D1 / L) ^ 2 := by
        dsimp only [D1]
        rw [div_pow, mul_pow, Real.sq_sqrt hG.le]
        ring
      exact hb.trans_eq he
    · intro z
      have hb := scalar_comp_directional_bound X.metric hu cutoffTransition cutoffTransition_contDiff
        hB1.le hB2.le (div_nonneg hW.le (sq_nonneg L)) (div_nonneg hG.le (sq_nonneg L))
        (fun s => (hBd s).1) (fun s => (hBd s).2) hder.1 hder.2 x z
      have he : B1 * (W / L ^ 2) + 2 * B2 * (G / L ^ 2) = D2 / L ^ 2 := by dsimp only [D2]; ring
      simpa only [he] using hb
  let v : ℝ → Pt X → ℝ := fun L => if hL : 0 < L then Classical.choose (hscale L hL) else fun _ => 0
  refine ⟨v, D1, D2, hD1, hD2, ?_⟩
  intro L hL
  simpa only [v, dif_pos hL] using Classical.choose_spec (hscale L hL)

end Yau.NodeProofs.P07Aux

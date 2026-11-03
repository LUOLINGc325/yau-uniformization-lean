import Yau.Proofs.F04MassCutoffCalculus
import Yau.Proofs.F04HermitianBounds

open Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint Yau.LeafProofs.L14Aux

theorem massCutoff_differential_bounds {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) :
    ∃ D : ℝ, 0 < D ∧ ∀ R : ℝ, 1 ≤ R → ∀ x,
      gradNormSq X.metric.form (massCutoff u R) x ≤ D ^ 2 / R ^ 2 ∧
        HermLE (((-(D / R ^ 2) : ℝ) : ℂ) • gMat X.metric.form x)
          (levi (massCutoff u R) x) ∧
        HermLE (levi (massCutoff u R) x)
          (((D / R ^ 2 : ℝ) : ℂ) • gMat X.metric.form x) := by
  obtain ⟨C, hC, hcontrol⟩ := hu.2.2.2
  obtain ⟨B, hB, hder⟩ := massProfile_derivative_bounds
  let D : ℝ := B * C + B * C ^ 2 + 1
  have hBC : 0 ≤ B * C := mul_nonneg hB.le hC.le
  have hBC2 : 0 ≤ B * C ^ 2 := mul_nonneg hB.le (sq_nonneg C)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hBCD : B * C ≤ D := by dsimp only [D]; linarith
  refine ⟨D, hD, ?_⟩
  intro R hR x
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hux : 0 < u x := lt_of_lt_of_le zero_lt_one (hu.2.2.1 x)
  have hG := LeafProofs.gMat_posDef X.metric.form x
  have hc := hcontrol x
  have hp₁ : |deriv massProfile (u x / R) / R| ≤ B / R := by
    rw [abs_div, abs_of_pos hRp]
    exact div_le_div_of_nonneg_right (hder _).1 hRp.le
  have hp₂ : |deriv (deriv massProfile) (u x / R) / R ^ 2| ≤ B / R ^ 2 := by
    rw [abs_div, abs_of_pos (sq_pos_of_pos hRp)]
    exact div_le_div_of_nonneg_right (hder _).2 (sq_nonneg R)
  constructor
  · rw [massCutoff_gradNormSq X.metric.form hu.1 R x]
    have hs : (deriv massProfile (u x / R) / R) ^ 2 ≤ (B / R) ^ 2 := by
      nlinarith [sq_abs (deriv massProfile (u x / R) / R), abs_nonneg (deriv massProfile (u x / R) / R),
        div_nonneg hB.le hRp.le]
    calc
      _ ≤ (deriv massProfile (u x / R) / R) ^ 2 * C ^ 2 :=
        mul_le_mul_of_nonneg_left hc.2.2.1 (sq_nonneg _)
      _ ≤ (B / R) ^ 2 * C ^ 2 := mul_le_mul_of_nonneg_right hs (sq_nonneg C)
      _ = (B * C) ^ 2 / R ^ 2 := by ring
      _ ≤ D ^ 2 / R ^ 2 := div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg R)
  · by_cases hRx : R ≤ u x
    · have hratio : C / u x ≤ C / R := div_le_div_of_nonneg_left hC.le hRp hRx
      have hcl : HermLE (((-(C / u x) : ℝ) : ℂ) • gMat X.metric.form x) (levi u x) := by
        simpa only [Complex.ofReal_neg, Complex.ofReal_div] using hc.2.2.2.1
      have hfirst := symmetric_real_smul_bound (gMat X.metric.form x) (levi u x)
        (C / u x) (deriv massProfile (u x / R) / R) hcl hc.2.2.2.2
      have hfb : |deriv massProfile (u x / R) / R| * (C / u x) ≤ B * C / R ^ 2 := by
        calc
          _ ≤ (B / R) * (C / R) :=
            mul_le_mul hp₁ hratio (div_nonneg hC.le hux.le) (div_nonneg hB.le hRp.le)
          _ = _ := by ring
      have hf := symmetric_bound_enlarge hG.posSemidef hfb hfirst.1 hfirst.2
      have houter := symmetric_rankOne_bound (gMat X.metric.form x) hG
        (manifoldComplexGradient u x) (sq_nonneg C) hc.2.2.1
      have hsecond := symmetric_real_smul_bound (gMat X.metric.form x)
        (Matrix.vecMulVec (star (manifoldComplexGradient u x)) (manifoldComplexGradient u x))
        (C ^ 2) (deriv (deriv massProfile) (u x / R) / R ^ 2) houter.1 houter.2
      have hsb : |deriv (deriv massProfile) (u x / R) / R ^ 2| * C ^ 2 ≤ B * C ^ 2 / R ^ 2 := by
        calc
          _ ≤ (B / R ^ 2) * C ^ 2 := mul_le_mul_of_nonneg_right hp₂ (sq_nonneg C)
          _ = _ := by ring
      have hs := symmetric_bound_enlarge hG.posSemidef hsb hsecond.1 hsecond.2
      have hadd := symmetric_bound_add hf.1 hf.2 hs.1 hs.2
      have hd : B * C / R ^ 2 + B * C ^ 2 / R ^ 2 ≤ D / R ^ 2 := by
        rw [← add_div]
        exact div_le_div_of_nonneg_right (by dsimp only [D]; linarith) (sq_nonneg R)
      have hh := symmetric_bound_enlarge hG.posSemidef hd hadd.1 hadd.2
      rw [← massCutoff_levi_formula hu.1 R x] at hh
      exact hh
    · have hflat := (massCutoff_flat_off_shell hu.1 hRp x (Or.inl (lt_of_not_ge hRx))).1
      rw [hflat]
      have hq : 0 ≤ D / R ^ 2 := div_nonneg hD.le (sq_nonneg R)
      constructor
      · simpa only [Complex.ofReal_zero, zero_smul] using
          hermLE_scalar_mono (gMat X.metric.form x) hG.posSemidef (show -(D / R ^ 2) ≤ 0 by linarith)
      · simpa only [Complex.ofReal_zero, zero_smul] using
          hermLE_scalar_mono (gMat X.metric.form x) hG.posSemidef hq

end Yau.F04Proof

import Yau.Proofs.F04MassCutoffBounds
import Yau.Proofs.F04PositiveWeightedCross

open Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint Yau.LeafProofs.L14Aux

def massProductError {n : ℕ} {M : ComplexManifold n}
    (u χ : M.Carrier → ℝ) (R : ℝ) (x : M.Carrier) : Herm n :=
  (χ x : ℂ) • levi (massCutoff u R) x +
    covectorCross (manifoldComplexGradient χ x) (manifoldComplexGradient (massCutoff u R) x)

theorem massProductError_identity {n : ℕ} {M : ComplexManifold n}
    {u χ : M.Carrier → ℝ} (hu : SmoothFn u) (hχ : SmoothFn χ) (R : ℝ) (x : M.Carrier) :
    levi (fun y => χ y * massCutoff u R y) x =
      (massCutoff u R x : ℂ) • levi χ x + massProductError u χ R x := by
  rw [levi_mul hχ (massCutoff_smooth hu R) x]
  simp only [massProductError, add_assoc]

theorem massProductError_flat {n : ℕ} {M : ComplexManifold n}
    {u χ : M.Carrier → ℝ} (hu : SmoothFn u) {R : ℝ} (hR : 0 < R)
    (x : M.Carrier) (hx : u x < R ∨ 2 * R < u x) : massProductError u χ R x = 0 := by
  have hh := massCutoff_flat_off_shell hu hR x hx
  simp only [massProductError, hh.1, hh.2, smul_zero, covectorCross, Matrix.vecMulVec_zero,
    star_zero, Matrix.zero_vecMulVec, add_zero]

theorem massProductError_bound {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) :
    ∃ D : ℝ, 0 < D ∧ ∀ (χ : Pt X → ℝ) (C : ℝ),
      (∀ x, 0 < χ x) → (∀ x, gradNormSq X.metric.form χ x ≤ (C * χ x / u x) ^ 2) →
      ∀ R : ℝ, 1 ≤ R → ∀ x, R ≤ u x →
        let E := D + C ^ 2 + D ^ 2
        HermLE (((-(E * χ x / R ^ 2) : ℝ) : ℂ) • gMat X.metric.form x)
          (massProductError u χ R x) ∧
        HermLE (massProductError u χ R x)
          (((E * χ x / R ^ 2 : ℝ) : ℂ) • gMat X.metric.form x) := by
  obtain ⟨D, hD, hb⟩ := massCutoff_differential_bounds X o u hu
  refine ⟨D, hD, ?_⟩
  intro χ C hχ hχgrad R hR x hRx
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hux : 0 < u x := lt_of_lt_of_le hRp hRx
  have hG := LeafProofs.gMat_posDef X.metric.form x
  have hc := hb R hR x
  have hp := symmetric_real_smul_bound (gMat X.metric.form x) (levi (massCutoff u R) x)
    (D / R ^ 2) (χ x) hc.2.1 hc.2.2
  rw [abs_of_pos (hχ x)] at hp
  have hx := positive_weight_covector_cross_bound (gMat X.metric.form x) hG
    (manifoldComplexGradient χ x) (manifoldComplexGradient (massCutoff u R) x) (hχ x)
  dsimp only at hx
  have hqχ : dualNormMat (gMat X.metric.form x) (WithLp.toLp 2 (manifoldComplexGradient χ x)) /
      χ x ≤ C ^ 2 * χ x / (u x) ^ 2 := by
    calc
      _ ≤ (C * χ x / u x) ^ 2 / χ x :=
        div_le_div_of_nonneg_right (hχgrad x) (hχ x).le
      _ = _ := by field_simp [(hχ x).ne', hux.ne']
  have hratio : C ^ 2 * χ x / (u x) ^ 2 ≤ C ^ 2 * χ x / R ^ 2 :=
    div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg C) (hχ x).le)
      (sq_pos_of_pos hRp) (by nlinarith)
  have hqc :
      dualNormMat (gMat X.metric.form x) (WithLp.toLp 2 (manifoldComplexGradient χ x)) / χ x +
          χ x * dualNormMat (gMat X.metric.form x)
            (WithLp.toLp 2 (manifoldComplexGradient (massCutoff u R) x)) ≤
        (C ^ 2 + D ^ 2) * χ x / R ^ 2 := by
    have hqp := mul_le_mul_of_nonneg_left hc.1 (hχ x).le
    have hh := add_le_add (hqχ.trans hratio) hqp
    calc
      _ ≤ C ^ 2 * χ x / R ^ 2 + χ x * (D ^ 2 / R ^ 2) := hh
      _ = _ := by ring
  have hcross := symmetric_bound_enlarge hG.posSemidef hqc hx.1 hx.2
  have hsum := symmetric_bound_add hp.1 hp.2 hcross.1 hcross.2
  have heq : χ x * (D / R ^ 2) + (C ^ 2 + D ^ 2) * χ x / R ^ 2 =
      (D + C ^ 2 + D ^ 2) * χ x / R ^ 2 := by ring
  rw [heq] at hsum
  simpa only [massProductError] using hsum

end Yau.F04Proof

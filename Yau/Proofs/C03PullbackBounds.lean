import Yau.Proofs.C03PullbackExtension

/-! The globally extended field retains a uniform lower matrix bound. -/

noncomputable section
open Set
open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem scalar_identity_HermLE (a b : ℝ) (hab : a ≤ b) :
    HermLE ((a : ℂ) • (1 : Herm n)) ((b : ℂ) • (1 : Herm n)) := by
  have H := (Matrix.PosSemidef.one : (1 : Herm n).PosSemidef).smul
    (Complex.zero_le_real.mpr (sub_nonneg.mpr hab))
  unfold HermLE
  convert H using 1
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_sub]
  ring

theorem blend_matrix_lower_bound (H : Herm n) (c t : ℝ)
    (hH : HermLE ((c : ℂ) • (1 : Herm n)) H) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    HermLE (((min c 1 : ℝ) : ℂ) • (1 : Herm n))
      ((t : ℂ) • H + ((1 - t : ℝ) : ℂ) • (1 : Herm n)) := by
  let d := min c 1
  let b := t * (c - d) + (1 - t) * (1 - d)
  have hd₁ : d ≤ c := min_le_left _ _
  have hd₂ : d ≤ 1 := min_le_right _ _
  have hb : 0 ≤ b := add_nonneg (mul_nonneg ht (sub_nonneg.mpr hd₁))
    (mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hd₂))
  have H₁ := hH.smul (Complex.zero_le_real.mpr ht)
  have H₂ := (Matrix.PosSemidef.one : (1 : Herm n).PosSemidef).smul
    (Complex.zero_le_real.mpr hb)
  unfold HermLE
  convert H₁.add H₂ using 1
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul]
  dsimp only [b, d]
  push_cast
  ring

theorem cutoffPullbackField_gMat (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r : ℝ) (hΦ : IsLocalBiholomorphism Φ r)
    (χ : ComplexVector n → ℝ) (hχ : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (hs : tsupport χ ⊆ Metric.ball (0 : ComplexVector n) r)
    (z : (ComplexEuclideanManifold n hn).Carrier) :
    gMat (cutoffPullbackField hn X Φ r hΦ χ hχ) z =
      (χ z : ℂ) • pullbackMat X.metric.form Φ z +
        ((1 - χ z : ℝ) : ℂ) • (1 : Herm n) := by
  have hpt : chartPt z z = z := by
    change extChartAt (ComplexModel n) (z : ComplexVector n) z = z
    rw [extChartAt_model_space_eq_id]
    rfl
  rw [gMat, hpt]
  ext a b
  exact cutoffPullbackField_hMat hn X Φ r hΦ χ hχ hs z z a b

theorem cutoffPullbackField_global_lower_bound (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r c : ℝ) (hΦ : IsLocalBiholomorphism Φ r)
    (χ : ComplexVector n → ℝ) (hχ : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (hs : tsupport χ ⊆ Metric.ball (0 : ComplexVector n) r)
    (hlo : ∀ z ∈ Metric.ball (0 : ComplexVector n) r,
      HermLE ((c : ℂ) • (1 : Herm n)) (pullbackMat X.metric.form Φ z))
    (z : (ComplexEuclideanManifold n hn).Carrier) :
    HermLE (((min c 1 : ℝ) : ℂ) • (1 : Herm n))
      (gMat (cutoffPullbackField hn X Φ r hΦ χ hχ) z) := by
  rw [cutoffPullbackField_gMat hn X Φ r hΦ χ hχ hs z]
  by_cases hz : z ∈ Metric.ball (0 : ComplexVector n) r
  · exact blend_matrix_lower_bound _ c _ (hlo z hz) (hχ z).1 (hχ z).2
  · have hzero : χ z = 0 := by
      by_contra hne
      exact hz (hs (subset_closure hne))
    simp only [hzero, Complex.ofReal_zero, zero_smul, sub_zero, Complex.ofReal_one,
      one_smul, zero_add]
    simpa only [Complex.ofReal_one, one_smul] using
      scalar_identity_HermLE (n := n) (min c 1) 1 (min_le_right c 1)

end Yau.Proofs.C03Aux

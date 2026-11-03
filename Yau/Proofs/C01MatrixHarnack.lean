import Yau.Proofs.C01SpacetimeCurvature
import Yau.Proofs.C01FlowTimeJets
import Yau.Proofs.C01LogTimeJets
import Yau.Proofs.C01TimeCurvatureAlgebra

/-! The original matrix differential Harnack expression, obtained from the
computed pure logarithmic-time curvature block of the same localized flow. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_matrix_harnack
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (x : Pt X) {t : ℝ} (ht : 0 < t) :
    (Matrix.of (fun a b => deriv (fun s => ricci (h s) x a b) t) +
      ricci (h t) x * (gMat (h t) x)⁻¹ * ricci (h t) x +
      ((t⁻¹ : ℝ) : ℂ) • ricci (h t) x).PosSemidef := by
  let w : ℂ := ((Real.log t / 2 : ℝ) : ℂ)
  let H := spacetimeMetricLine h x (chartPt x x) 0 w 1
  let H₁ : Herm n := fun i j => wirt (fun p => H p i j) 0 1
  let H₂ : Herm n := fun i j => wirtBar (fun p => H p i j) 0 1
  let H₁₂ : Herm n := fun i j => wirt (fun p => wirtBar (fun q => H q i j) p 1) 0 1
  let A := ricci (h t) x
  let D := Matrix.of (fun i j => deriv (fun s => ricci (h s) x i j) t)
  have htime : Real.exp (2 * w.re) = t := by
    have he : 2 * w.re = Real.log t := by
      simp only [w, Complex.ofReal_re]
      ring
    rw [he, Real.exp_log ht]
  have hH₀ : H 0 = gMat (h t) x := by
    simp only [H, spacetimeMetricLine, zero_mul, zero_smul, add_zero, gMat, htime]
  have hH₁ : H₁ = -((t : ℂ) • A) := by
    ext i j
    have hd : HasDerivAt (fun s => gMat (h s) x i j) (-(A i j))
        (Real.exp (2 * (w + (0 : ℂ)).re)) := by
      simpa only [add_zero, htime] using localizedFlow_gMat_hasDerivAt hflow x ht i j
    have hp := (logarithmic_time_wirtinger (fun s => gMat (h s) x i j) w 0 _ hd).1
    simpa only [H₁, H, spacetimeMetricLine, mul_one, smul_zero, add_zero,
      gMat, htime, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, mul_neg] using hp
  have hH₂ : H₂ = -((t : ℂ) • A) := by
    ext i j
    have hd : HasDerivAt (fun s => gMat (h s) x i j) (-(A i j))
        (Real.exp (2 * (w + (0 : ℂ)).re)) := by
      simpa only [add_zero, htime] using localizedFlow_gMat_hasDerivAt hflow x ht i j
    have hp := (logarithmic_time_wirtinger (fun s => gMat (h s) x i j) w 0 _ hd).2
    simpa only [H₂, H, spacetimeMetricLine, mul_one, smul_zero, add_zero,
      gMat, htime, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, mul_neg] using hp
  have hH₁₂ : H₁₂ = -((t : ℂ) • A) - ((t ^ 2 : ℝ) : ℂ) • D := by
    ext i j
    have hd : HasDerivAt (fun s => -(ricci (h s) x i j)) (-(D i j))
        (Real.exp (2 * (w + (0 : ℂ)).re)) := by
      simpa only [add_zero, htime, D, Matrix.of_apply, Pi.neg_apply] using!
        (localizedFlow_ricci_hasDerivAt hflow x ht i j).neg
    have hp := logarithmic_time_mixed (fun s => gMat (h s) x i j)
      (fun s => -(ricci (h s) x i j)) w 0 _
      (fun s hs => localizedFlow_gMat_hasDerivAt hflow x hs i j) hd
    simpa only [H₁₂, H, spacetimeMetricLine, mul_one, smul_zero, add_zero,
      gMat, htime, A, D, Matrix.of_apply, Matrix.sub_apply, Matrix.neg_apply,
      Matrix.smul_apply, smul_eq_mul, mul_neg, sub_eq_add_neg, Complex.ofReal_pow] using hp
  have hcurvature : ∀ v : Fin n → ℂ,
      0 ≤ (star v ⬝ᵥ ((-H₁₂ + H₂ * (H 0)⁻¹ * H₁) *ᵥ v)).re :=
    localizedFlow_spacetime_curvature_nonneg hflow hjoint x (chartPt x x) 0
      (mem_extChartAt_target (I := ComplexModel n) x) w 1
  have hfactor : -H₁₂ + H₂ * (H 0)⁻¹ * H₁ =
      (t : ℂ) • A + ((t ^ 2 : ℝ) : ℂ) • (D + A * (gMat (h t) x)⁻¹ * A) := by
    rw [hH₁₂, hH₂, hH₁, hH₀]
    have ht₂ : (t : ℂ) * (t : ℂ) = ((t ^ 2 : ℝ) : ℂ) := by push_cast; ring
    have hprod : (-((t : ℂ) • A)) * (gMat (h t) x)⁻¹ * (-((t : ℂ) • A)) =
        ((t ^ 2 : ℝ) : ℂ) • (A * (gMat (h t) x)⁻¹ * A) := by
      simp only [← neg_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        neg_mul_neg, ht₂]
    rw [hprod]
    simp only [neg_sub, neg_neg, smul_add]
    abel

  apply matrix_harnack_of_time_curvature (gMat (h t) x) A D
    (Alignment.Y03Proof.hMat_posDef (h t) x (chartPt x x)
      (mem_extChartAt_target (I := ComplexModel n) x))
    (localizedFlow_ricci_isHermitian hflow x ht)
    (localizedFlow_ricci_timeDerivative_isHermitian hflow x ht) ht
  intro v
  have hp := hcurvature v
  rwa [hfactor] at hp

end Yau.NodeProofs.C01Aux

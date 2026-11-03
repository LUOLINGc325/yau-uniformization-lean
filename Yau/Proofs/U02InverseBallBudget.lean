import Yau.Proofs.U02ModelSeparation

/-! The original coefficient and inverse-linear bounds pay for the
actual Cauchy error and the smaller target radius on the same clock. -/

open scoped Topology Matrix
open Filter

noncomputable section
namespace Yau.NodeProofs.U02Proof
open Yau Blueprint

theorem models_H_inverse_linear_weighted {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {rho : STF X} {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {d : ℕ} {hm Cd Dg : ℝ} {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv)
    {B eps : ℝ} (hB : 0 ≤ B) (heps : 0 < eps) :
    ∀ᶠ k in atTop, B * matOpNorm (H k).linearPart⁻¹ ≤ Real.exp (eps * rho o (tk k)) := by
  obtain ⟨Cp, hCp⟩ := hp.2.2.2.2.2.2.2.2.1
  filter_upwards [nat_polynomial_absorption hp.2.1 B Cp heps] with k hk
  exact (mul_le_mul_of_nonneg_left (hCp k).2.1 hB).trans hk

theorem inverse_ball_cauchy_budget {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {rho : STF X} {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {d : ℕ} {hm Cd Dg : ℝ} {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv)
    {gamma gammap : ℝ} (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1) (hgap : gamma < gammap) :
    ∀ᶠ k in atTop,
      let r := Real.exp (-gamma * rho o (tk k))
      matOpNorm (H k).linearPart⁻¹ *
        ((2 * (H k).coeffNorm * r ^ 2 + Real.exp (-6 * rho o (tk k))) / (r / 2)) ≤ 1 / 4 ∧
      matOpNorm (H k).linearPart⁻¹ * Real.exp (-gammap * rho o (tk k)) ≤ r / 4 := by
  obtain ⟨eta, heta, hcoeff⟩ := hp.2.2.2.2.2.2.2.1
  filter_upwards [models_H_inverse_linear_exp hp (by positivity : 0 < gamma / 4),
    subexponential_absorption hp.2.1 heta 32 (by positivity : 0 < gamma / 4),
    models_H_inverse_linear_weighted hp (by norm_num : (0 : ℝ) ≤ 16) (by norm_num : (0 : ℝ) < 1 / 4),
    models_H_inverse_linear_weighted hp (by norm_num : (0 : ℝ) ≤ 4) (sub_pos.mpr hgap),
    (tendsto_atTop.1 hp.2.1) 0] with k hlin hcoef hlin16 hlin4 hsk
  let s := rho o (tk k)
  let r := Real.exp (-gamma * s)
  let Ai := matOpNorm (H k).linearPart⁻¹
  have hr : 0 < r := Real.exp_pos _
  have hA : 0 ≤ Ai := norm_nonneg _
  have hC0 : 0 ≤ (H k).coeffNorm := Yau.Proofs.Y02Aux.coeffNorm_nonneg _
  have hcoef32 : 32 * (H k).coeffNorm ≤ Real.exp ((gamma / 4) * s) :=
    (mul_le_mul_of_nonneg_left (hcoeff k).1 (by norm_num)).trans hcoef
  have hfirst : 32 * Ai * (H k).coeffNorm * r ≤ 1 := by
    calc
      _ = Ai * (32 * (H k).coeffNorm) * r := by ring
      _ ≤ Real.exp ((gamma / 4) * s) * Real.exp ((gamma / 4) * s) * r := by gcongr
      _ ≤ 1 := by
        dsimp only [r]
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_one_iff.mpr
        nlinarith
  have hsecond : 16 * Ai * Real.exp (-6 * s) / r ≤ 1 := by
    calc
      _ ≤ Real.exp ((1 / 4) * s) * Real.exp (-6 * s) / r := by gcongr
      _ ≤ 1 := by
        dsimp only [r]
        rw [← Real.exp_add, ← Real.exp_sub]
        apply Real.exp_le_one_iff.mpr
        nlinarith
  refine ⟨?_, ?_⟩
  · change Ai * ((2 * (H k).coeffNorm * r ^ 2 + Real.exp (-6 * s)) / (r / 2)) ≤ 1 / 4
    have he : Ai * ((2 * (H k).coeffNorm * r ^ 2 + Real.exp (-6 * s)) / (r / 2)) =
        (32 * Ai * (H k).coeffNorm * r) / 8 + (16 * Ai * Real.exp (-6 * s) / r) / 8 := by
      field_simp
      ring
    rw [he]
    nlinarith
  · change Ai * Real.exp (-gammap * s) ≤ r / 4
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
    calc
      _ = (4 * Ai) * Real.exp (-gammap * s) := by ring
      _ ≤ Real.exp ((gammap - gamma) * s) * Real.exp (-gammap * s) :=
        mul_le_mul_of_nonneg_right hlin4 (Real.exp_pos _).le
      _ = r := by
        dsimp only [r]
        rw [← Real.exp_add]
        congr 1
        ring

end Yau.NodeProofs.U02Proof

import Yau.Proofs.U02LinearAbsorption
import Yau.Proofs.U02PolynomialLipschitz
import Yau.Proofs.U02SmallPolynomials
import Yau.Proofs.U02JetDecay

/-! Quantitative separation for the original corrected polynomial maps. -/

open scoped Topology Matrix
open Filter Metric

noncomputable section
namespace Yau.NodeProofs.U02Proof
open Yau Blueprint

theorem models_H_inverse_linear_exp {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {rho : STF X} {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {d : ℕ} {hm Cd Dg : ℝ} {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv)
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ k in atTop, matOpNorm (H k).linearPart⁻¹ ≤ Real.exp (eps * rho o (tk k)) := by
  obtain ⟨Cp, hCp⟩ := hp.2.2.2.2.2.2.2.2.1
  filter_upwards [nat_polynomial_absorption hp.2.1 1 Cp heps] with k hk
  exact (hCp k).2.1.trans (by simpa only [one_mul] using hk)

theorem models_H_lower_distance {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {rho : STF X} {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {d : ℕ} {hm Cd Dg : ℝ} {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv)
    {a : ℝ} (ha : 0 < a) :
    ∀ᶠ k in atTop, ∀ u v : ComplexVector n,
      ‖u‖ ≤ Real.exp (-a * rho o (tk k)) →
      ‖v‖ ≤ Real.exp (-a * rho o (tk k)) →
      ‖u - v‖ ≤ 2 * matOpNorm (H k).linearPart⁻¹ * ‖(H k).eval u - (H k).eval v‖ := by
  obtain ⟨eta, heta, hcoeff⟩ := hp.2.2.2.2.2.2.2.1
  filter_upwards [models_H_inverse_linear_exp hp (by positivity : 0 < a / 4),
    subexponential_absorption hp.2.1 heta 16 (by positivity : 0 < a / 4),
    eventually_exp_decay_lt hp.2.1 ha (by norm_num : (0 : ℝ) < 1 / 2),
    (tendsto_atTop.1 hp.2.1) 0] with k hlin hcoef hr hsk
  have hc : 16 * (H k).coeffNorm ≤ Real.exp ((a / 4) * rho o (tk k)) :=
    (mul_le_mul_of_nonneg_left (hcoeff k).1 (by norm_num)).trans hcoef
  have hsmall : matOpNorm (H k).linearPart⁻¹ *
      (8 * (H k).coeffNorm * Real.exp (-a * rho o (tk k))) ≤ 1 / 2 := by
    have hA0 : 0 ≤ matOpNorm (H k).linearPart⁻¹ := norm_nonneg _
    have hC0 : 0 ≤ (H k).coeffNorm := Yau.Proofs.Y02Aux.coeffNorm_nonneg _
    have hprod := mul_le_mul hlin hc (by positivity) (Real.exp_pos _).le
    have he : Real.exp ((a / 4) * rho o (tk k)) *
        Real.exp ((a / 4) * rho o (tk k)) * Real.exp (-a * rho o (tk k)) ≤ 1 := by
      rw [← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_one_iff.mpr (by nlinarith)
    have hh := mul_le_mul_of_nonneg_right hprod (Real.exp_pos (-a * rho o (tk k))).le
    nlinarith
  intro u v hu hv
  have hn := hp.2.2.2.2.1 k
  exact polynomial_lower_distance (H k) hn.1 hn.2.2.2.2.2.1 (Real.exp_pos _)
    (by linarith) hsmall
    (by simpa only [mem_closedBall, dist_zero_right] using hu)
    (by simpa only [mem_closedBall, dist_zero_right] using hv)

end Yau.NodeProofs.U02Proof

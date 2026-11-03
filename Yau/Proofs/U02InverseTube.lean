import Yau.Proofs.U02SqrtAbsorption
import Yau.Proofs.U02Subexponential
import Yau.Proofs.U02Spacing
import Yau.Proofs.U02JetDecay
import Yau.Proofs.U02LinearPart
import Yau.Proofs.U02PolynomialLipschitz

/-! The inverse tube estimate for the original inverse polynomial maps.
The matrix bound and the coefficient bound are both extracted from the
original models; no inverse derivative field is supplied. -/

open scoped Topology Matrix
open Filter Metric

noncomputable section
namespace Yau.NodeProofs.U02Proof

open Yau Blueprint
open Yau.Proofs.Y02Aux

theorem rpow_absorption_sqrt {s : ℕ → ℝ} (hs : Tendsto s atTop atTop)
    (p : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ k in atTop, (s k) ^ p ≤ Real.exp (eps * Real.sqrt (s k)) := by
  filter_upwards [polynomial_absorption_sqrt hs 1 |p| heps,
    (tendsto_atTop.1 hs) 1] with k hk hsk
  calc
    (s k) ^ p ≤ (s k) ^ |p| := Real.rpow_le_rpow_of_exponent_le hsk (le_abs_self p)
    _ ≤ (1 + s k) ^ |p| :=
      Real.rpow_le_rpow (by linarith) (by linarith) (abs_nonneg p)
    _ ≤ _ := by simpa only [one_mul] using hk

theorem models_step_tendsto {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {rho : STF X} {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {d : ℕ} {hm Cd Dg : ℝ} {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv) :
    Tendsto (fun k => rho o (tk (k + 1)) - rho o (tk k)) atTop atTop := by
  obtain ⟨ch, hch, K, hK⟩ := hp.2.2.2.1
  have hlim := (Real.tendsto_sqrt_atTop.comp hp.2.1).const_mul_atTop hch
  apply Filter.tendsto_atTop.2
  intro R
  filter_upwards [eventually_atTop.2 ⟨K, fun k hk => (hK k hk).1⟩,
    (tendsto_atTop.1 hlim) R] with k hk hlarge
  exact hlarge.trans hk

theorem models_inverse_linear_bound {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {rho : STF X} {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {d : ℕ} {hm Cd Dg : ℝ} {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv) :
    ∀ᶠ k in atTop, matOpNorm (Ginv k).linearPart ≤
      Real.exp (3 * (rho o (tk (k + 1)) - rho o (tk k)) / 4) := by
  obtain ⟨ch, hch, K, hK⟩ := hp.2.2.2.1
  obtain ⟨Cp, hCp⟩ := hp.2.2.2.2.2.2.2.2.1
  filter_upwards [rpow_absorption_sqrt hp.2.1 Cp (by positivity : 0 < ch / 4),
    eventually_atTop.2 ⟨K, fun k hk => (hK k hk).1⟩] with k hk hstep
  have hk' : rho o (tk k) ^ Cp ≤ Real.exp ((ch / 4) * Real.sqrt (rho o (tk k))) := by
    simpa only [Real.rpow_natCast] using hk
  have hn := hp.2.2.2.2.1 k
  have hlin : matOpNorm (Ginv k).linearPart ≤
      rho o (tk k) ^ Cp * Real.exp ((rho o (tk (k + 1)) - rho o (tk k)) / 2) := by
    rw [automorphism_inverse_linearPart hn.2.2.2.2.1 hn.2.2.2.1]
    exact (hCp k).2.2
  calc
    _ ≤ _ := hlin
    _ ≤ Real.exp ((ch / 4) * Real.sqrt (rho o (tk k))) *
        Real.exp ((rho o (tk (k + 1)) - rho o (tk k)) / 2) :=
      mul_le_mul_of_nonneg_right hk' (Real.exp_pos _).le
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith

theorem models_inverse_nonlinear_bound {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {rho : STF X} {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {d : ℕ} {hm Cd Dg : ℝ} {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv)
    {nu : ℝ} (hnu : 0 < nu)
    (hpaid : |Cd| * (Real.exp hm - 1) ≤ nu / 4) :
    ∀ᶠ k in atTop, 8 * (Ginv k).coeffNorm * Real.exp (-nu * rho o (tk (k + 1))) ≤ 1 := by
  let s := fun k => rho o (tk k)
  obtain ⟨eta, heta, hcoeff⟩ := hp.2.2.2.2.2.2.2.1
  have hbound := subexponential_times_decay hp.2.1 heta 8 (3 * nu / 4) 0 (by positivity)
  filter_upwards [hbound, models_unit_spacing hp, (tendsto_atTop.1 hp.2.1) 0]
    with k hk hstep hsk
  have hDelta : 0 ≤ s (k + 1) - s k := by linarith [hstep.1]
  have hDeltaUpper : s (k + 1) - s k ≤ (Real.exp hm - 1) * s k := by
    nlinarith [hstep.2]
  have hCdDelta : Cd * (s (k + 1) - s k) ≤ (nu / 4) * s k := by
    have ha := mul_le_mul_of_nonneg_right (le_abs_self Cd) hDelta
    have hb := mul_le_mul_of_nonneg_left hDeltaUpper (abs_nonneg Cd)
    have hc := mul_le_mul_of_nonneg_right hpaid hsk
    nlinarith
  have hnuStep : nu * s k ≤ nu * s (k + 1) :=
    mul_le_mul_of_nonneg_left (by linarith [hstep.1]) hnu.le
  have hQ : (Ginv k).coeffNorm ≤
      Real.exp (Cd * (s (k + 1) - s k) + eta k * s k) :=
    (le_add_of_nonneg_left (coeffNorm_nonneg (G k))).trans (hcoeff k).2.2
  calc
    8 * (Ginv k).coeffNorm * Real.exp (-nu * s (k + 1)) ≤
        8 * Real.exp (Cd * (s (k + 1) - s k) + eta k * s k) *
          Real.exp (-nu * s (k + 1)) := by gcongr
    _ = 8 * Real.exp (Cd * (s (k + 1) - s k) + eta k * s k - nu * s (k + 1)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ 8 * Real.exp (eta k * s k - (3 * nu / 4) * s k) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by norm_num)
    _ = 8 * Real.exp (eta k * s k) * Real.exp (-(3 * nu / 4) * s k) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ 1 := by simpa only [neg_zero, zero_mul, Real.exp_zero] using hk

theorem models_inverse_tube {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {rho : STF X} {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {d : ℕ} {hm Cd Dg : ℝ} {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv)
    {nu : ℝ} (hnu : 0 < nu)
    (hpaid : |Cd| * (Real.exp hm - 1) ≤ nu / 4) :
    ∀ᶠ k in atTop, ∀ u v : ComplexVector n,
      ‖u‖ < Real.exp (-nu * rho o (tk (k + 1))) →
      ‖v‖ < Real.exp (-nu * rho o (tk (k + 1))) →
      ‖(Ginv k).eval u - (Ginv k).eval v‖ ≤
        Real.exp (rho o (tk (k + 1)) - rho o (tk k)) * ‖u - v‖ := by
  let s := fun k => rho o (tk k)
  have hsnext : Tendsto (fun k => s (k + 1)) atTop atTop :=
    hp.2.1.comp (tendsto_add_atTop_nat 1)
  filter_upwards [models_inverse_linear_bound hp, models_inverse_nonlinear_bound hp hnu hpaid,
    eventually_exp_decay_lt hsnext hnu (by norm_num : (0 : ℝ) < 1 / 2),
    (tendsto_atTop.1 (models_step_tendsto hp)) (4 * Real.log 2)]
    with k hlin hnonlinear hrsmall hlarge
  have hDelta : 0 ≤ s (k + 1) - s k := by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hExp1 : 1 ≤ Real.exp (3 * (s (k + 1) - s k) / 4) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hExp2 : 2 ≤ Real.exp ((s (k + 1) - s k) / 4) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr (by linarith)
  have hsum : matOpNorm (Ginv k).linearPart +
      8 * (Ginv k).coeffNorm * Real.exp (-nu * s (k + 1)) ≤
      Real.exp (s (k + 1) - s k) := by
    calc
      _ ≤ Real.exp (3 * (s (k + 1) - s k) / 4) + 1 := add_le_add hlin hnonlinear
      _ ≤ 2 * Real.exp (3 * (s (k + 1) - s k) / 4) := by linarith
      _ ≤ Real.exp ((s (k + 1) - s k) / 4) *
          Real.exp (3 * (s (k + 1) - s k) / 4) :=
        mul_le_mul_of_nonneg_right hExp2 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  intro u v hu hv
  have hn := hp.2.2.2.2.1 k
  have hQ := automorphism_inverse_fixesZero hn.2.2.2.2.1 hn.2.2.2.1
  have hR : 2 * Real.exp (-nu * s (k + 1)) ≤ 1 := by linarith
  have hh := polynomial_lipschitz_small_ball (Ginv k) hQ (Real.exp_pos _) hR
    (by simpa only [mem_closedBall, dist_zero_right] using hu.le)
    (by simpa only [mem_closedBall, dist_zero_right] using hv.le)
  exact hh.trans (mul_le_mul_of_nonneg_right hsum (norm_nonneg _))

end Yau.NodeProofs.U02Proof

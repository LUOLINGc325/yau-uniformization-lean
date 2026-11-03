import Yau.Proofs.U02PolynomialGlobalBounds
import Yau.Proofs.U02Subexponential
import Yau.Proofs.U02Spacing

/-! Absorb the literal coefficient budget of the jet conjugacy error.
The fixed degree is supplied by the original `PolynomialModels` predicate. -/

open scoped Topology
open Filter

noncomputable section
namespace Yau.NodeProofs.U02Proof

open Yau Blueprint
open Yau.Proofs.Y02Aux

theorem models_jet_budget {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {rho : STF X} {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {d : ℕ} {hm Cd Dg : ℝ} {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv)
    (hdelta : Real.exp hm - 1 ≤ 1)
    (hpaid : |Cd| * (Real.exp hm - 1) ≤ 1 / 8) {B : ℝ} (hB : 1 ≤ B) :
    ∀ᶠ k in atTop,
      (H (k + 1)).coeffNorm * B ^ Nat.ceil Dg + ((G k).comp (H k)).coeffNorm ≤
        Real.exp (rho o (tk k)) := by
  let s := fun k => rho o (tk k)
  let D := Nat.ceil Dg
  let delta := Real.exp hm - 1
  obtain ⟨eta, heta, hcoeff⟩ := hp.2.2.2.2.2.2.2.1
  have hs : Tendsto s atTop atTop := hp.2.1
  have hetaNext : Tendsto (fun k => eta (k + 1)) atTop (𝓝 0) :=
    heta.comp (tendsto_add_atTop_nat 1)
  have heta1 : Tendsto (fun k => 2 * |eta (k + 1)|) atTop (𝓝 0) := by
    simpa using hetaNext.abs.const_mul 2
  have heta2 : Tendsto (fun k => ((D : ℝ) + 1) * |eta k|) atTop (𝓝 0) := by
    simpa using heta.abs.const_mul ((D : ℝ) + 1)
  have hfirst := subexponential_absorption hs heta1 (B ^ D) (by norm_num : (0 : ℝ) < 1 / 4)
  have hsecond := subexponential_absorption hs heta2 ((2 : ℝ) ^ D)
    (by norm_num : (0 : ℝ) < 1 / 8)
  have hsum := subexponential_absorption hs
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) 2
    (by norm_num : (0 : ℝ) < 3 / 4)
  filter_upwards [hfirst, hsecond, hsum, models_unit_spacing hp,
    (tendsto_atTop.1 hs) 0] with k h1 h2 h3 hstep hsk
  have hstep' : 1 ≤ s (k + 1) - s k ∧ s (k + 1) ≤ (1 + delta) * s k := hstep
  have hsnext : 0 ≤ s (k + 1) := by linarith [hstep'.1]
  have hs2 : s (k + 1) ≤ 2 * s k := by
    have hh := mul_le_mul_of_nonneg_right hdelta hsk
    dsimp only [delta] at hstep'
    nlinarith [hstep'.2]
  have hnext : eta (k + 1) * s (k + 1) ≤ (2 * |eta (k + 1)|) * s k := by
    have hle := mul_le_mul_of_nonneg_right (le_abs_self (eta (k + 1))) hsnext
    have hh := mul_le_mul_of_nonneg_left hs2 (abs_nonneg (eta (k + 1)))
    nlinarith
  have hHnext : (H (k + 1)).coeffNorm * B ^ D ≤ Real.exp ((1 / 4) * s k) := by
    calc
      _ ≤ Real.exp ((2 * |eta (k + 1)|) * s k) * B ^ D :=
        mul_le_mul_of_nonneg_right
          ((hcoeff (k + 1)).1.trans (Real.exp_le_exp.mpr hnext))
          (pow_nonneg (zero_le_one.trans hB) _)
      _ = B ^ D * Real.exp ((2 * |eta (k + 1)|) * s k) := mul_comm _ _
      _ ≤ _ := h1
  have hDelta : 0 ≤ s (k + 1) - s k := by linarith [hstep'.1]
  have hDeltaUpper : s (k + 1) - s k ≤ delta * s k := by nlinarith [hstep'.2]
  have hCdDelta : Cd * (s (k + 1) - s k) ≤ s k / 8 := by
    have ha := mul_le_mul_of_nonneg_right (le_abs_self Cd) hDelta
    have hb := mul_le_mul_of_nonneg_left hDeltaUpper (abs_nonneg Cd)
    have hc := mul_le_mul_of_nonneg_right hpaid hsk
    dsimp only [delta] at hb
    nlinarith
  have hEta : eta k * s k ≤ |eta k| * s k :=
    mul_le_mul_of_nonneg_right (le_abs_self (eta k)) hsk
  have hExp : 1 ≤ Real.exp (|eta k| * s k) :=
    Real.one_le_exp_iff.mpr (mul_nonneg (abs_nonneg _) hsk)
  have hH : 1 + (H k).coeffNorm ≤ 2 * Real.exp (|eta k| * s k) := by
    have hh := (hcoeff k).1.trans (Real.exp_le_exp.mpr hEta)
    linarith
  have hD : (G k).degree ≤ D :=
    degree_le_natCeil (hp.2.2.2.2.2.2.1 k).2.1
  have hpow : (1 + (H k).coeffNorm) ^ (G k).degree ≤
      (2 * Real.exp (|eta k| * s k)) ^ D :=
    (pow_le_pow_left₀ (by linarith [coeffNorm_nonneg (H k)]) hH _).trans
      (pow_le_pow_right₀ (by linarith) hD)
  have hG : (G k).coeffNorm ≤ Real.exp (Cd * (s (k + 1) - s k) + eta k * s k) :=
    (le_add_of_nonneg_right (coeffNorm_nonneg (Ginv k))).trans (hcoeff k).2.2
  have hComp : ((G k).comp (H k)).coeffNorm ≤ Real.exp ((1 / 4) * s k) := by
    calc
      _ ≤ (G k).coeffNorm * (1 + (H k).coeffNorm) ^ (G k).degree := comp_coeffNorm_le _ _
      _ ≤ Real.exp (s k / 8 + |eta k| * s k) *
          (2 * Real.exp (|eta k| * s k)) ^ D :=
        mul_le_mul (hG.trans (Real.exp_le_exp.mpr (by linarith))) hpow
          (pow_nonneg (by linarith [coeffNorm_nonneg (H k)]) _) (Real.exp_pos _).le
      _ = ((2 : ℝ) ^ D * Real.exp ((((D : ℝ) + 1) * |eta k|) * s k)) *
          Real.exp (s k / 8) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        calc
          _ = (2 : ℝ) ^ D *
              (Real.exp (s k / 8 + |eta k| * s k) *
                Real.exp ((D : ℝ) * (|eta k| * s k))) := by ring
          _ = (2 : ℝ) ^ D *
              Real.exp ((((D : ℝ) + 1) * |eta k|) * s k + s k / 8) := by
            rw [← Real.exp_add]
            congr 2
            ring
          _ = _ := by rw [Real.exp_add]; ring
      _ ≤ Real.exp ((1 / 8) * s k) * Real.exp (s k / 8) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = Real.exp ((1 / 4) * s k) := by
        rw [← Real.exp_add]
        congr 1
        ring
  change (H (k + 1)).coeffNorm * B ^ D + ((G k).comp (H k)).coeffNorm ≤ Real.exp (s k)
  calc
    _ ≤ 2 * Real.exp ((1 / 4) * s k) := by linarith
    _ ≤ Real.exp ((3 / 4) * s k) * Real.exp ((1 / 4) * s k) :=
      mul_le_mul_of_nonneg_right (by simpa using h3) (Real.exp_pos _).le
    _ = Real.exp (s k) := by rw [← Real.exp_add]; congr 1; ring

end Yau.NodeProofs.U02Proof

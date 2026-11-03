import Yau.Proofs.Y01CoordinateData
import Yau.Proofs.Y01CenterConjugacy
import Yau.Proofs.Y01EndpointGrowth

/-! One polynomial exponent bounds the actual primary matrices and every
matrix conjugate of the original center derivative on the same clock. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux

variable {n : ℕ}

theorem center_bounds_from_original_changes
    {X : KahlerManifold n} {o : Pt X} {h : Flow X} {ρ : STF X}
    {r₀ r₁ σ Cgeo Cb t₀ : ℝ} {Φ : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {f : ℝ → Pt X → ComplexVector n}
    (hcharts : ShrinkingCharts X o h ρ r₀ r₁ σ Cgeo Cb t₀ Φ F f)
    {tk : ℕ → ℝ} {E : Frames n} (hE : SingularFrames F tk E)
    {Qclock : ℕ → ℝ} {N j₀ : ℕ} {M hm scale K eps : ℝ}
    (hhm : 0 < hm) (hgrid : GridLayout Qclock N M hm j₀)
    (hdom : ∀ k, t₀ ≤ tk k)
    (hρ : ∀ k, ρ o (tk k) = gridClock Qclock N M hm j₀ k)
    (hs2 : ∀ k, 2 ≤ gridClock Qclock N M hm j₀ k)
    {L : Changes n} {C c : ℝ} (hc : 0 < c)
    (hL : ∀ k, Regular Qclock N M (macroAt Qclock N M hm j₀ k) →
      ChangeAt (diagonal F tk E) (weight Qclock N M hm scale K eps j₀ (rate F tk E))
        (macroAt Qclock N M hm j₀) (macroClock hm) C c L k) :
    let s := gridClock Qclock N M hm j₀
    let reg := fun k => Regular Qclock N M (macroAt Qclock N M hm j₀ k)
    let T := primaryDerivative reg E L
    ∃ Cp : ℝ, 1 ≤ Cp ∧ ∀ k,
      matOpNorm (T k) ≤ (1 + s k) ^ Cp ∧ matOpNorm (T k)⁻¹ ≤ (1 + s k) ^ Cp ∧
      ∀ B : Herm n, T (k + 1) * derivativeMatrix (F (tk k) (tk (k + 1))) = B * T k →
        matOpNorm B⁻¹ ≤ s k ^ Cp * Real.exp ((s (k + 1) - s k) / 2) := by
  let s := gridClock Qclock N M hm j₀
  let reg := fun k => Regular Qclock N M (macroAt Qclock N M hm j₀ k)
  let T := primaryDerivative reg E L
  obtain ⟨p, hp, hT⟩ := primaryDerivative_polynomial_bounds (F := F) (tk := tk) (E := E)
    (Q := Qclock) (N := N) (j₀ := j₀) (M := M) (hm := hm) (scale := scale) (K := K)
    (eps := eps) (L := L) (C := C) (c := c) hE hhm hgrid hc hL
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  obtain ⟨q, hpq, hprod⟩ := endpoint_real_power_product hm p hp0
  have hs k : 1 ≤ s k := (by norm_num : (1 : ℝ) ≤ 2).trans (hs2 k)
  have hTk k : matOpNorm (T k) ≤ (1 + s k) ^ p := by
    linarith [hT k, matOpNorm_nonneg_own (T k)⁻¹]
  have hTik k : matOpNorm (T k)⁻¹ ≤ (1 + s k) ^ p := by
    linarith [hT k, matOpNorm_nonneg_own (T k)]
  obtain ⟨ch, Ch, hch, hCh, hsteps⟩ := hgrid.2.2.2.2.2
  refine ⟨q, hp.trans hpq, ?_⟩
  intro k
  have hPower : (1 + s k) ^ p ≤ (1 + s k) ^ q :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [hs k]) hpq
  refine ⟨(hTk k).trans hPower, (hTik k).trans hPower, ?_⟩
  intro B hconj
  have hTunit : IsUnit (T k) := primaryDerivative_isUnit hE hL k
  have hMatrix := model_inverse_bound_of_conjugacy hTunit hconj
  have hOriginal := (original_transition_inverse_bound hcharts (hdom k) (hE k).2.1.le).2
  have hDinv : matOpNorm (derivativeMatrix (F (tk k) (tk (k + 1))))⁻¹ ≤
      Real.exp ((s (k + 1) - s k) / 2) := by
    simpa only [hρ] using hOriginal
  have hFirst : matOpNorm (T k) * matOpNorm (derivativeMatrix (F (tk k) (tk (k + 1))))⁻¹ ≤
      (1 + s k) ^ p * Real.exp ((s (k + 1) - s k) / 2) :=
    mul_le_mul (hTk k) hDinv (matOpNorm_nonneg_own _) (Real.rpow_nonneg (by linarith [hs k]) _)
  have hSecond := mul_le_mul hFirst (hTik (k + 1)) (matOpNorm_nonneg_own (T (k + 1))⁻¹)
    (mul_nonneg (Real.rpow_nonneg (by linarith [hs k]) _) (Real.exp_pos _).le)
  have hStep : s (k + 1) ≤ Real.exp hm * s k := by
    have h := (hsteps k).2.1
    change s (k + 1) - s k ≤ (Real.exp hm - 1) * s k at h
    nlinarith
  have hEndpoints := hprod (s k) (s (k + 1)) (hs2 k) (by linarith [hs (k + 1)]) hStep
  calc
    matOpNorm B⁻¹ ≤ (1 + s k) ^ p * Real.exp ((s (k + 1) - s k) / 2) * (1 + s (k + 1)) ^ p :=
      hMatrix.trans hSecond
    _ = ((1 + s k) ^ p * (1 + s (k + 1)) ^ p) * Real.exp ((s (k + 1) - s k) / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hEndpoints (Real.exp_pos _).le

end Yau.Proofs.Y01Aux

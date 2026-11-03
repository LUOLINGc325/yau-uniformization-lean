import Yau.Proofs.Y05TransitionPolynomials
import Yau.Proofs.Y05GridCoefficientSums
import Yau.Proofs.Y05SeriesCocycle

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux Filter
open scoped Topology ContDiff

variable {n : ℕ}

theorem exists_coherent_log_data {X : KahlerManifold n}
    {o : Pt X} {h : Flow X} {ρ : STF X} {r₀ r₁ σ C Cb t₀ : ℝ}
    {Φ : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n}
    (hc : ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f)
    {tk : ℕ → ℝ} (htk : StrictMono tk) (hlate : ∀ k, t₀ ≤ tk k)
    (hdiv : Tendsto (fun k => ρ o (tk k)) atTop atTop) (hs : ∀ k, 0 < ρ o (tk k))
    {ch Q : ℝ} (hch : 0 < ch) (hQ : 0 ≤ Q)
    (hstepLo : ∀ k, ch * Real.sqrt (ρ o (tk k)) ≤ ρ o (tk (k + 1)) - ρ o (tk k))
    (hstepHi : ∀ k, ρ o (tk (k + 1)) - ρ o (tk k) ≤ Q * ρ o (tk k)) (d : ℕ) :
    ∃ (r : ℝ) (P : ℕ → ComplexVector n → ℂ)
      (B : ℕ → ℕ → MvPolynomial (Fin n) ℂ) (ell : ℕ → MvPolynomial (Fin n) ℂ) (H : ℝ),
      r ≤ r₁ ∧ 0 < r ∧ 0 < H ∧
      (∀ k, P k 0 = 0 ∧ DifferentiableOn ℂ (P k) (Metric.ball 0 r) ∧
        ∀ z ∈ Metric.ball (0 : ComplexVector n) r,
          Complex.exp (P k z) = transitionDet F (tk k) (tk (k + 1)) z /
            transitionDet F (tk k) (tk (k + 1)) 0) ∧
      (∀ k l, k ≤ l → (B k l).totalDegree ≤ d ∧ (B k l).coeff 0 = 0 ∧
        ScalarJetEq (scalarEval (B k l)) (fun z => P l (F (tk k) (tk l) z)) d) ∧
      (∀ k, (ell k).totalDegree ≤ d ∧ (ell k).coeff 0 = 0 ∧
        (∀ a, HasSum (fun r : ℕ => (B k (k + r)).coeff a) ((ell k).coeff a)) ∧
        ScalarJetEq (scalarEval (ell k))
          (fun z => P k z + scalarEval (ell (k + 1)) (F (tk k) (tk (k + 1)) z)) d) ∧
      ∀ k, polynomialCoeffNorm (ell k) ≤ H * (1 + ρ o (tk k)) ^ 4 := by
  let s := fun k => ρ o (tk k)
  have hr : 0 < r₁ := hc.1
  have hσ : 0 < σ := hc.2.2.1
  have htrans := hc.2.2.2.2.2.1
  have hcomp := hc.2.2.2.2.2.2.1
  have hsm : Monotone s := (strictMono_nat_of_lt_succ (fun k => by
    have hp := mul_pos hch (Real.sqrt_pos.2 (hs k))
    have H := hstepLo k
    change s k < s (k + 1)
    dsimp [s]
    linarith)).monotone
  have hTa (k l : ℕ) (hkl : k ≤ l) : AnalyticAt ℂ (F (tk k) (tk l)) 0 :=
    Yau.NodeProofs.U02Proof.holomorphic_analyticOnNhd Metric.isOpen_ball
      (htrans (tk k) (tk l) (hlate k) (htk.monotone hkl)).1 0 (Metric.mem_ball_self hr)
  have hT0 (k l : ℕ) (hkl : k ≤ l) : F (tk k) (tk l) 0 = 0 :=
    (htrans (tk k) (tk l) (hlate k) (htk.monotone hkl)).2.2.1
  obtain ⟨P, hPdata, hPjets⟩ := exists_shrinking_transition_logs hc htk hlate hsm
  obtain ⟨K, hK, hPjet⟩ := hPjets d
  obtain ⟨Cj, hCj, hFjet⟩ := shrinking_grid_global_jet_decay hc htk hlate hs hsm hdiv d
  obtain ⟨D, L, B, hD, hL, hB⟩ := exists_transition_log_polynomials
    (T := fun k l => F (tk k) (tk l)) (P := P) (s := s)
    (by positivity : 0 < r₁ / 2) hCj hK.le hs hsm hTa hT0
    (fun k => (hPdata k).2.1) (fun k => (hPdata k).1) hPjet hFjet
  obtain ⟨ell, H, hH, hEll⟩ := exists_grid_coefficient_sums
    (s := s) (B := B) (le_trans zero_le_one hD) hσ hQ hL hch hs hsm hstepLo hstepHi
    (fun k l hkl => (hB k l hkl).1) (fun k l hkl => (hB k l hkl).2.1)
    (fun k l hkl => (hB k l hkl).2.2.2)
  have hPa (k : ℕ) : AnalyticAt ℂ (P k) 0 :=
    U02AnalyticAux.analyticOnNhd_of_complex_contDiffOn_infty Metric.isOpen_ball
      (Yau.Blueprint.V03Proof.complex_holomorphic_contDiffOn Metric.isOpen_ball
        (hPdata k).2.1) 0 (Metric.mem_ball_self (by positivity))
  have hself (k : ℕ) : F (tk k) (tk k) =ᶠ[𝓝 0] id := by
    filter_upwards [Metric.ball_mem_nhds (0 : ComplexVector n) hr] with z hz
    exact Yau.NodeProofs.U02Proof.shrinking_transition_self hc (hlate k) hz
  have hCocycle := coefficient_tail_scalar_cocycle hTa hT0 hPa
    (fun k j l hkj hjl => hcomp (tk k) (tk j) (tk l) (hlate k)
      (htk.monotone hkj) (htk.monotone hjl)) hself
    (fun k l hkl => (hB k l hkl).2.2.1) (fun k l hkl => (hB k l hkl).1)
    (fun k => (hEll k).1) (fun k => (hEll k).2.2.1)
  refine ⟨r₁ / 2, P, B, ell, H, by linarith, by positivity, hH, hPdata,
    fun k l hkl => ⟨(hB k l hkl).1, (hB k l hkl).2.1, (hB k l hkl).2.2.1⟩,
    fun k => ⟨(hEll k).1, (hEll k).2.1, (hEll k).2.2.1, hCocycle k⟩,
    fun k => (hEll k).2.2.2⟩

end Yau.Proofs.Y05Aux

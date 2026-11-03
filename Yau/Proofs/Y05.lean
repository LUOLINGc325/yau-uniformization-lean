import Yau.Proofs.Y05CoherentLogData
import Yau.Proofs.Y05VolumeCoordinates
import Yau.Proofs.Y05VolumeCancellation
import spec.CHAIN.CONTRACTS

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux Filter
open scoped Topology ContDiff

set_option maxHeartbeats 800000 in
theorem Y05_proved : Yau.Blueprint.Y05 := by
  change Alignment.Y05
  intro n hn X o h U Pflow ρ r₀ r₁ σ C Cb t₀ Φ F f hFlow hWindows hCharts
    d hd hm hhm hhm1 tk htk hlate
  dsimp only
  intro hdiv hs hgrid
  obtain ⟨ch, hch, hsteps⟩ := hgrid
  have hd1 : 1 ≤ d := by omega
  let s := fun k => ρ o (tk k)
  have hsm : Monotone s := (strictMono_nat_of_lt_succ (fun k => by
    have hp := mul_pos hch (Real.sqrt_pos.2 (hs k))
    have H := (hsteps k).1
    change s k < s (k + 1)
    dsimp [s]
    linarith)).monotone
  have hQ : 0 ≤ Real.exp hm - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hhm.le)
  obtain ⟨r, logs, B, ell, H, hrr₁, hr, hH, hLogs, hB, hEll, hEllNorm⟩ :=
    exists_coherent_log_data hCharts htk hlate hdiv hs hch hQ
      (fun k => (hsteps k).1) (fun k => (hsteps k).2) (d - 1)
  let last : Fin n := ⟨n - 1, by omega⟩
  have hEllGrowth : HasPolynomialBound s (fun k => polynomialCoeffNorm (ell k)) :=
    ⟨H, hH.le, 4, hEllNorm⟩
  obtain ⟨E, A, Ainv, hCoordinates, hGrowth⟩ := exists_volume_coordinates hd1 last
    (fun k => (hEll k).2.1) hs hsm hEllGrowth
  have htrans := hCharts.2.2.2.2.2.1
  have hModels (k : ℕ) : ∃ V : PolyMap n, V.degree ≤ d ∧ IsConstantVolumeJet V d ∧
      GermJetEq (fun z => (A (k + 1)).eval (F (tk k) (tk (k + 1)) ((Ainv k).eval z)))
        V.eval d := by
    rcases hCoordinates k with ⟨hEdeg, hE0, hEjet, hAeq, hA0, hI0, hAlin, hAdeg, hIdeg, hRight, hLeft⟩
    rcases hCoordinates (k + 1) with
      ⟨hEnextdeg, hEnext0, hEnextjet, hAnextEq, hAnext0, hInext0, hAnextlin,
        hAnextdeg, hInextdeg, hNextRight, hNextLeft⟩
    have hT := htrans (tk k) (tk (k + 1)) (hlate k) (htk.monotone (Nat.le_succ k))
    have hFa : AnalyticAt ℂ (F (tk k) (tk (k + 1))) 0 :=
      Yau.NodeProofs.U02Proof.holomorphic_analyticOnNhd Metric.isOpen_ball hT.1
        0 (Metric.mem_ball_self hCharts.1)
    have hPa : AnalyticAt ℂ (logs k) 0 :=
      U02AnalyticAux.analyticOnNhd_of_complex_contDiffOn_infty Metric.isOpen_ball
        (Yau.Blueprint.V03Proof.complex_holomorphic_contDiffOn Metric.isOpen_ball (hLogs k).2.1)
        0 (Metric.mem_ball_self hr)
    have hc : transitionDet F (tk k) (tk (k + 1)) 0 ≠ 0 :=
      jacobian_det_ne_zero ((hT.2.1 0 (Metric.mem_ball_self hCharts.1)).1)
    have hlog : ∀ᶠ z in 𝓝 0, Complex.exp (logs k z) =
        LinearMap.det (fderiv ℂ (F (tk k) (tk (k + 1))) z).toLinearMap /
          transitionDet F (tk k) (tk (k + 1)) 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ComplexVector n) hr] with z hz
      exact (hLogs k).2.2 z hz
    apply exists_normalized_volume_model hd1 hFa hT.2.2.1 hPa hc hlog
      (E₀ := E k) (E₁ := E (k + 1)) (L₀ := ell k) (L₁ := ell (k + 1))
      (A₀ := A k) (A₁ := A (k + 1)) (I := Ainv k)
    · rw [hAeq]
      exact jacDet_volumeMap last (E k)
    · rw [hAnextEq]
      exact jacDet_volumeMap last (E (k + 1))
    · exact hAnext0
    · exact hI0
    · exact hRight
    · exact (hEll k).2.2.2
    · exact hEjet
    · exact hEnextjet
  choose V hVdeg hVconst hVjet using hModels
  refine ⟨r, logs, B, ell, E, A, Ainv, V, hrr₁, hr, hLogs, hB, ?_, ?_⟩
  · intro k
    rcases hCoordinates k with ⟨hEdeg, hE0, hEjet, hAeq, hA0, hI0, hAlin, hAdeg, hIdeg, hRight, hLeft⟩
    exact ⟨(hEll k).1, (hEll k).2.1, (hEll k).2.2.1, (hEll k).2.2.2,
      hEdeg, hEjet, hAeq, hA0, hI0, hAlin, hAdeg, hIdeg, hRight, hLeft,
      hVdeg k, hVconst k, hVjet k⟩
  · simpa only [polynomialCoeffNorm] using hGrowth

theorem Y05_contract_proved
    (_hC07 : Yau.BlueprintContracts.C07_contract) : Yau.BlueprintContracts.Y05_contract :=
  Y05_proved

end Yau.Proofs.Y05Aux

import Yau.Proofs.Y01BaseModels
import Yau.Proofs.Y01RegularTail
import Yau.Proofs.Y01TailModels
import Yau.Proofs.Y01OriginalVolume
import Yau.Proofs.Y01ZeroDimension

/-! The original Y01 producer, with dimension/order constants chosen before
all geometry and one construction restricted to every later regular start. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Yau.Proofs.Y01Aux

open Filter Yau.Blueprint Yau.Blueprint.Alignment Yau.BlueprintContracts
open Yau.Blueprint.Alignment.Y03Proof Yau.NodeProofs.Y07Aux

theorem Y01_of_original_predecessors
    (hY02 : Y02_contract) (hY03 : Y03_contract) (hY05 : Y05_contract)
    (hY06 : Y06_contract) (hY07 : Y07_contract) : Y01_contract := by
  change CanonicalModelConstruction
  change CanonicalGridTail at hY07
  intro n d hd2
  by_cases hn : n = 0
  · subst n
    refine ⟨1, 1, by norm_num, le_rfl, ?_⟩
    intro X o h U P ρ r₀ r₁ σ C Cb t₀ Φ F f hflow hwin hjoint hcharts
    exact False.elim (original_Y03_zero_dimension_impossible hY03 X o h U P ρ
      r₀ r₁ σ C Cb t₀ Φ F f hflow hwin hjoint hcharts)
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hd : 1 ≤ d := by omega
    obtain ⟨Dd, Craw, hrealize⟩ := hY02 n d hd2
    obtain ⟨Dsix, hDsix1, hsix⟩ := hY06 n d hd2
    let Dtotal := max d (max Dd Dsix)
    have hDd : d ≤ Dtotal := le_max_left _ _
    have hDrealize : Dd ≤ Dtotal := (le_max_left _ _).trans (le_max_right _ _)
    have hDsix : Dsix ≤ Dtotal := (le_max_right _ _).trans (le_max_right _ _)
    have hD1 : 1 ≤ Dtotal := hDsix1.trans hDsix
    refine ⟨1 + |Craw|, Dtotal, by positivity, hD1, ?_⟩
    intro X o h U P ρ r₀ r₁ σ C Cb t₀ Φ F f hflow hwin hjoint hcharts
    change Alignment.Y03 at hY03
    obtain ⟨time, s₀, a₀, b₀, hclock, ha₀, ha₁, hb₀, hrate, hwidth⟩ :=
      hY03 n X o h U P ρ r₀ r₁ σ C Cb t₀ Φ F f hflow hwin hjoint hcharts
    refine ⟨time, s₀, a₀, b₀, hclock, ha₀, ha₁, hb₀, hrate, ?_⟩
    intro hm hhm hhm1
    obtain ⟨N, hN, hwindow, hthreshold⟩ := hwidth hm hhm hhm1
    obtain ⟨M, hM, hpay, hgap⟩ := exists_flag_threshold Dtotal N hm b₀
    refine ⟨N, M, hN, hwindow, hM, hpay, hgap, ?_⟩
    let Qclock := sampledSpeed o h time hm
    obtain ⟨scale, K, eps, b, hscale, hK, heps, hepsSmall, hb,
      jGeom, hjGeom, hdomainGeom, hgrids⟩ := hthreshold M hM
    refine ⟨scale, K, eps, b, hscale, hK, heps, hepsSmall, hb, ?_⟩
    obtain ⟨BF, Td, hBF, hbound⟩ := uniform_transition_jet_bound hcharts d
    have hmacro := macroClock_tendsto hm hhm
    have hphysical := hclock.2.2.2.comp hmacro
    obtain ⟨JT, hJT⟩ := tendsto_atTop_atTop.1 hphysical Td
    obtain ⟨JS, hJS⟩ := tendsto_atTop_atTop.1 hmacro 2
    obtain ⟨jBase, hjBase, hRegBase⟩ := exists_late_regular_endpoint hrate hhm hN hD1
      hM hb₀ hpay hgap (max jGeom (max JT JS))
    have hBaseGeom : jGeom ≤ jBase := (le_max_left _ _).trans hjBase
    have hBaseT : JT ≤ jBase := ((le_max_left _ _).trans (le_max_right _ _)).trans hjBase
    have hBaseS : JS ≤ jBase := ((le_max_right _ _).trans (le_max_right _ _)).trans hjBase
    obtain ⟨hgrid, hdomain, E, hE, horder, htrace, hwindowBase, hweightsBase, hruns⟩ :=
      hgrids jBase hBaseGeom hRegBase
    let s := gridClock Qclock N M hm jBase
    let tk := fun k => time (s k)
    let reg := fun k => Regular Qclock N M (macroAt Qclock N M hm jBase k)
    obtain ⟨L, CAlign, cAlign, hCAlign, hcAlign, hLdata⟩ := alignment_solution_from_runs hruns
    have hp := physical_grid_properties hclock hgrid (fun k => (hdomain k).1)
    have htk : StrictMono tk := hp.1
    have hρ : ∀ k, ρ o (tk k) = s k := hp.2.2.1
    have hTd0 : Td ≤ tk 0 := by
      change Td ≤ time (gridClock Qclock N M hm jBase 0)
      rw [hgrid.1]
      exact hJT jBase hBaseT
    have hs2 : ∀ k, 2 ≤ s k := by
      intro k
      have hzero : 2 ≤ s 0 := by
        change 2 ≤ gridClock Qclock N M hm jBase 0
        rw [hgrid.1]
        exact hJS jBase hBaseS
      exact hzero.trans (hgrid.2.1.monotone (Nat.zero_le k))
    have hs : ∀ k, 1 ≤ s k := fun k => (by norm_num : (1 : ℝ) ≤ 2).trans (hs2 k)
    have hFnorm : ∀ k, jetNorm (F (tk k) (tk (k + 1))) d ≤ BF := by
      intro k
      exact hbound _ _ (hTd0.trans (htk.monotone (Nat.zero_le k)))
        (htk.monotone (Nat.le_succ k))
    have hJets := regular_transition_polynomial_bound (reg := reg) (s := s) hBF hbound htk hTd0 hs
    obtain ⟨r, logs, B, ell, Evol, A, Ainv, V, hrr, hVol⟩ :=
      original_volume_on_grid hY05 hnPos hd2 hflow hwin hcharts hclock hhm hhm1 hgrid hdomain
    have hOrigInput := original_grid_transition_inputs hcharts htk (fun k => (hdomain k).2) hρ hrr
    obtain ⟨kLate, hRuns, hDecay⟩ := hsix F tk Qclock N jBase M hm scale K eps b b₀ E L r
      ⟨n - 1, by omega⟩ logs B ell Evol A Ainv V hhm hhm1 hscale hK heps hepsSmall hb hb₀
      hgrid hE horder hwindowBase hweightsBase hOrigInput.1 hVol hOrigInput.2
      ⟨CAlign, cAlign, hCAlign, hcAlign, hLdata⟩ hJets
    obtain ⟨Cq, hCq, hGlobal, hFinite, hInfinite⟩ := hRuns
    obtain ⟨qsol, hQ⟩ := hGlobal
    obtain ⟨R, Rinv, hRdata, hModelsBase⟩ := base_polynomial_models_from_original_outputs
      hd hDd hDrealize hDsix hrealize hcharts hE hhm hgrid (fun k => (hdomain k).2) hρ hs2
      hcAlign (fun k hk => (hLdata k hk).1) hVol hQ hFnorm
    let T := primaryDerivative reg E L
    let H := fun k => coordinateJet d (A k) (qsol.correction k) (T k)
    let Hinv := fun k => inverseCoordinateJet d (Ainv k) (qsol.inverseJet k) (T k)
    let J := fun k => if reg (k + 1) then alignedJump E L k else 1
    let active := fun k => kLate ≤ k ∧ reg k
    let G := assembledModel active J qsol R
    let Ginv := assembledInverseModel active J qsol Rinv
    refine ⟨jBase + kLate + 1, by omega, ?_⟩
    intro j₀ hj₀ hReg₀
    have hbBase : jBase ≤ j₀ := by omega
    have hNewGeom : jGeom ≤ j₀ := hBaseGeom.trans hbBase
    obtain ⟨hnew, hdomainNew, hNewFrames⟩ := hgrids j₀ hNewGeom hReg₀
    let off := offset Qclock N M hm jBase j₀
    have hOff : kLate ≤ off := canonical_offset_beyond_threshold Qclock N M hm (by omega)
    have hTkTail : (fun k => time (gridClock Qclock N M hm j₀ k)) =
        (fun k => tk (off + k)) := by
      funext k
      exact congrArg time (hY07 Qclock N M hm jBase j₀ hbBase hgrid hnew k)
    refine ⟨hnew, hdomainNew, (fun k => H (off + k)), (fun k => Hinv (off + k)),
      (fun k => G (off + k)), (fun k => Ginv (off + k)), (fun k => qsol.model (off + k)),
      shiftFrames off E, shiftChanges off L, ?_, ?_, ?_, ?_⟩
    · change PolynomialModels X o ρ F d hm (1 + |Craw|) (Dtotal : ℝ)
        (fun k => time (gridClock Qclock N M hm j₀ k)) _ _ _ _
      rw [hTkTail]
      exact polynomialModels_canonical_tail hY07 hhm hbBase hgrid hnew hρ hModelsBase
    · change WindowRateBounds Qclock N M hm b₀ j₀
        (rate F (fun k => time (gridClock Qclock N M hm j₀ k)) (shiftFrames off E))
      rw [hTkTail]
      have hμ : rate F (fun k => tk (off + k)) (shiftFrames off E) =
          (fun k => rate F tk E (off + k)) := by
        funext k i
        exact rate_shift F tk E off k i
      rw [hμ]
      exact windowRateBounds_tail hbBase hnew hwindowBase
    · change WeightEstimates Qclock N M hm scale K eps b j₀
        (rate F (fun k => time (gridClock Qclock N M hm j₀ k)) (shiftFrames off E))
      rw [hTkTail]
      have hμ : rate F (fun k => tk (off + k)) (shiftFrames off E) =
          (fun k => rate F tk E (off + k)) := by
        funext k i
        exact rate_shift F tk E off k i
      rw [hμ]
      exact weightEstimates_tail hbBase hnew hweightsBase
    · change RegularModelCompatibility F (fun k => time (gridClock Qclock N M hm j₀ k))
        Qclock N M hm scale K eps j₀ Dtotal (shiftFrames off E) (shiftChanges off L)
        (fun k => H (off + k)) (fun k => G (off + k)) (fun k => Ginv (off + k))
        (fun k => qsol.model (off + k))
      rw [hTkTail]
      exact regularModelCompatibility_from_original_tail hbBase hnew hReg₀ hOff
        (max_le hDrealize hDsix) hE horder hCAlign hcAlign hLdata hVol hd hQ
        (fun k => ⟨(hRdata k).2.2.1, (hRdata k).2.2.2.1⟩)

end Yau.Proofs.Y01Aux

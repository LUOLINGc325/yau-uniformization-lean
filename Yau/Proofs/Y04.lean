import Yau.Proofs.Y04BadCharging
import Yau.Proofs.Y04ForwardDegree
import spec.CHAIN.CONTRACTS

/-! Exact Y04 assembly, conditional only on the original Y01 producer. -/

noncomputable section

open Yau Yau.Blueprint Yau.Blueprint.Alignment

namespace Yau.Proofs

open Yau.Blueprint.Alignment.Y04Proof

theorem Y04_of_originalY01
    (hY01 : Yau.BlueprintContracts.Y01_contract) :
    Yau.BlueprintContracts.Y04_contract := by
  change CanonicalModelConstruction at hY01
  change Alignment.Y04
  intro n d hd
  obtain ⟨Cd, Dstar, hCd, hD, hgeometry⟩ := hY01 n d hd
  refine ⟨Cd, Dstar, hCd, hD, ?_⟩
  intro X o h U P ρ r₀ r₁ σ C Cb t₀ Φ F f hflow hwin hjoint hcharts
  obtain ⟨time, s₀, a₀, b₀, hclock, ha₀, ha₁, hb₀, hrate, hwidth⟩ :=
    hgeometry X o h U P ρ r₀ r₁ σ C Cb t₀ Φ F f hflow hwin hjoint hcharts
  refine ⟨time, s₀, a₀, b₀, hclock, ha₀, ha₁, hb₀, hrate, ?_⟩
  intro hm hhm hhm1
  obtain ⟨N, M, hN, hNwindow, hM, hpay, hgap,
    scale, K, eps, b, hscale, hK, heps, hepsSmall, hb,
    Jmodel, hJmodel, hmodels⟩ := hwidth hm hhm hhm1
  let Q := sampledSpeed o h time hm
  obtain ⟨jBound, hNjBound, hclockBound, hcharge⟩ :=
    exists_badCharging_bound hrate hhm hN hD hM hb₀ hpay hgap
  obtain ⟨Jreset, hJreset, hreset⟩ := exists_reset_index (M := M) hb₀
  let jLate := max Jmodel (max (jBound+N+1) Jreset)
  have hjLate : max N jBound < jLate := by
    dsimp [jLate]
    omega
  refine ⟨N, M, hN, hNwindow, hM, hpay, hgap,
    jBound, hNjBound, hclockBound, hcharge,
    scale, K, eps, b, hscale, hK, heps, hepsSmall, hb,
    jLate, hjLate, ?_⟩
  intro j₀ hj₀ hreg₀
  have hmodelStart : Jmodel ≤ j₀ := by dsimp [jLate] at hj₀; omega
  have htailStart : jBound+N ≤ j₀ := by dsimp [jLate] at hj₀; omega
  have hresetStart : Jreset ≤ j₀ := by dsimp [jLate] at hj₀; omega
  obtain ⟨hgrid, hdomain, H, Hinv, G, Ginv, g, E, L,
    hPM, hwindow, hweights, hcompat⟩ := hmodels j₀ hmodelStart hreg₀
  obtain ⟨B, hB, hdegree⟩ := macro_degree_bound
    hN hD hM hhm hscale hK hb₀ htailStart hreg₀
    (fun j hj => hreset j (hresetStart.trans hj))
    hcharge hgrid hwindow hweights hcompat
  have hgood : ∀ J, ∃ j, max J jBound ≤ j ∧
      Q j ≤ 3*Real.exp hm*macroClock hm j := hcharge.2.2.2.2.2.2
  have hforward := forwardDegreeControl_of_macro_bound hB hdegree hgood
  exact ⟨hgrid, hdomain, H, Hinv, G, Ginv, g, E, L,
    hPM, hwindow, hweights, hcompat, ⟨B, hB, hdegree⟩, hforward⟩

end Yau.Proofs

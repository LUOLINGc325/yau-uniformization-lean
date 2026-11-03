import Yau.Proofs.Y06NormalizedRuns
import Yau.Proofs.Y06ClockAnalysis
import Yau.Proofs.Y06GeometricBudget
import spec.CHAIN.CONTRACTS

/-! The original Y06 contract, with dimension/order degree chosen before
all geometric input and a single late threshold for every required run. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open Filter Yau.Blueprint Yau.Blueprint.Alignment Yau.BlueprintContracts
open scoped Topology

theorem Y06_of_original_predecessors (hY02 : Y02_contract) : Y06_contract := by
  classical
  change Alignment.Y06
  intro n d hd2
  have hd : 1 ≤ d := by omega
  refine ⟨d ^ (n + 1), one_le_pow₀ hd, ?_⟩
  intro F tk Qclock N j₀ M hm scale K eps b b₀ Eframes L r last logs B ell Evol A Ainv V
  dsimp only
  intro hhm hhm1 hscale hK heps hepsSmall hb hb₀ hgrid hE horder hwindow hweights
    hF hVol hdet hChanges hjets
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le last.val) last.isLt
  obtain ⟨k₀, Ab, CT, c, hAb, hCT, hc, hbudget, hT, hJunit⟩ :=
    GeometricBudget.geometric_budget hn hhm hb hgrid hE hweights hF hVol hdet hChanges hjets
  let s := gridClock Qclock N M hm j₀
  let j := macroAt Qclock N M hm j₀
  let reg := fun k => Regular Qclock N M (j k)
  let w := weight Qclock N M hm scale K eps j₀ (rate F tk Eframes)
  let J := fun k => if reg (k + 1) then alignedJump Eframes L k else 1
  let a := fun k => (1 + (j k : ℝ)) ^ CT * Real.exp (-c * Real.sqrt (s k) / (j k : ℝ) ^ 2)
  have ha : ∀ k, 0 ≤ a k := fun k => mul_nonneg (Real.rpow_nonneg (by positivity) CT) (Real.exp_pos _).le
  have halim : Tendsto a atTop (𝓝 0) := grid_decay_tendsto_zero hhm hc hCT hgrid
  obtain ⟨Lb, hLb, hstep⟩ := regular_sqrt_increment hhm hgrid
  obtain ⟨CL, cL, hCL, hcL, hL⟩ := hChanges
  have hbud : ∀ k, k₀ ≤ k → reg k →
      polySize (normalizedPolynomial V Eframes L k) ≤ Real.exp (Ab * Real.sqrt (s k)) ∧
      polySize (linearPolynomial (J k)) ≤ Real.exp (Ab * Real.sqrt (s k)) ∧
      polySize (linearPolynomial (J k)⁻¹) ≤ Real.exp (Ab * Real.sqrt (s k)) ∧
      polySize (linearPolynomial (diagonal F tk Eframes k)) ≤ Real.exp (Ab * Real.sqrt (s k)) ∧
      polySize (linearPolynomial (diagonal F tk Eframes k)⁻¹) ≤ Real.exp (Ab * Real.sqrt (s k)) := by
    intro k hk hreg
    obtain ⟨hP, hJ, hJi, hD, hDi, hid⟩ := hbudget k hk hreg
    exact ⟨hP, hJ, hJi, hD, hDi⟩
  obtain ⟨kLate, hkLate, hruns⟩ := normalized_runs_of_budgets hE hVol hd (hY02 n d hd2) hF
    (fun k hk => (hL k hk).1) J a k₀ hAb hLb (fun k => gridClock_one_le hhm k) ha halim
    hstep hJunit (fun k hk i => (hweights.1 k i hk).2.2.1) hbud hT
  refine ⟨kLate, hruns, ?_⟩
  intro m hm2 hmd
  refine ⟨CT, c, hc, ?_⟩
  intro k hk hreg X hX
  exact hT m hm2 hmd k (hkLate.trans hk) hreg X hX

end Yau.Proofs.Y06Aux

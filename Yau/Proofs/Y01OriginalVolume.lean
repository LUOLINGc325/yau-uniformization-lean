import Yau.Proofs.Y01PreparedGrid

/-! Instantiate the original Y05 producer on the literal canonical grid;
the physical volume clock is identified by the original ClockParameter. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Filter Yau.Blueprint Yau.Blueprint.Alignment Yau.Blueprint.Alignment.Y03Proof

variable {n d N j₀ : ℕ} {Q : ℕ → ℝ} {M hm : ℝ}

theorem original_volume_on_grid
    (hY05 : Yau.BlueprintContracts.Y05_contract) (hn : 0 < n) (hd : 2 ≤ d)
    {X : KahlerManifold n} {o : Pt X} {h : Flow X} {U P ρ : STF X}
    {r₀ r₁ σ C Cb t₀ : ℝ} {Φ : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {f : ℝ → Pt X → ComplexVector n}
    (hflow : FlowStage X o h U P ρ) (hwin : RicciWindows X o h ρ)
    (hcharts : ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f)
    {time : ℝ → ℝ} {s₀ : ℝ} (hclock : ClockParameter X o h ρ time s₀)
    (hhm : 0 < hm) (hhm1 : hm < 1) (hgrid : GridLayout Q N M hm j₀)
    (hdomain : ∀ k, s₀ ≤ gridClock Q N M hm j₀ k ∧
      t₀ ≤ time (gridClock Q N M hm j₀ k)) :
    ∃ (r : ℝ) (logs : ℕ → ComplexVector n → ℂ)
      (B : ℕ → ℕ → MvPolynomial (Fin n) ℂ) (ell E : ℕ → MvPolynomial (Fin n) ℂ)
      (A Ainv V : ℕ → PolyMap n), r ≤ r₁ ∧
      CoherentVolume F (fun k => time (gridClock Q N M hm j₀ k))
        (gridClock Q N M hm j₀) d r ⟨n - 1, by omega⟩ logs B ell E A Ainv V := by
  let tk := fun k => time (gridClock Q N M hm j₀ k)
  have hp := physical_grid_properties hclock hgrid (fun k => (hdomain k).1)
  have hsfun : (fun k => ρ o (tk k)) = gridClock Q N M hm j₀ := funext hp.2.2.1
  have hclockEq k : ρ o (tk k) = gridClock Q N M hm j₀ k := hp.2.2.1 k
  obtain ⟨ch, Ch, hch, hCh, hsteps⟩ := hgrid.2.2.2.2.2
  have hlower : ∃ ch : ℝ, 0 < ch ∧ ∀ k,
      ch * Real.sqrt (ρ o (tk k)) ≤ ρ o (tk (k + 1)) - ρ o (tk k) ∧
      ρ o (tk (k + 1)) - ρ o (tk k) ≤ (Real.exp hm - 1) * ρ o (tk k) := by
    refine ⟨ch, hch, ?_⟩
    intro k
    rw [hclockEq k, hclockEq (k + 1)]
    exact ⟨(hsteps k).1, (hsteps k).2.1⟩
  have hpos : ∀ k, 0 < ρ o (tk k) := by
    intro k
    rw [hclockEq k]
    exact gridClock_positive hgrid k
  have hv := hY05 n hn X o h U P ρ r₀ r₁ σ C Cb t₀ Φ F f hflow hwin hcharts
    d hd hm hhm hhm1 tk hp.1 (fun k => (hdomain k).2) hp.2.2.2 hpos hlower
  simpa only [hsfun] using hv

theorem original_grid_transition_inputs
    {X : KahlerManifold n} {o : Pt X} {h : Flow X} {ρ : STF X}
    {r₀ r₁ σ C Cb t₀ : ℝ} {Φ : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {f : ℝ → Pt X → ComplexVector n}
    (hcharts : ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f)
    {tk s : ℕ → ℝ} (hmono : StrictMono tk) (hdom : ∀ k, t₀ ≤ tk k)
    (hs : ∀ k, ρ o (tk k) = s k) {r : ℝ} (hrr : r ≤ r₁) :
    (∀ k, F (tk k) (tk (k + 1)) 0 = 0 ∧
      DifferentiableOn ℂ (F (tk k) (tk (k + 1))) (Metric.ball 0 r)) ∧
    (∀ k, ‖transitionDet F (tk k) (tk (k + 1)) 0‖ =
      Real.exp (-(s (k + 1) - s k) / 2)) := by
  have hstep k := hcharts.2.2.2.2.2.1 (tk k) (tk (k + 1)) (hdom k)
    (hmono.monotone (Nat.le_succ k))
  refine ⟨?_, ?_⟩
  · intro k
    exact ⟨(hstep k).2.2.1, (hstep k).1.mono (Metric.ball_subset_ball hrr)⟩
  · intro k
    simpa only [transitionDet, hs] using (hstep k).2.2.2.2.2.1

end Yau.Proofs.Y01Aux

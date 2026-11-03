import Yau.Proofs.Y03RayleighFrame
import Yau.Proofs.Y03ClockIncrement
import Yau.Proofs.Y03GridWindows

/-! Preserve the original b₀ window bounds, uniformly before choosing a grid start. -/

open scoped Topology Matrix
open Set

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ} {X : KahlerManifold n}

theorem windowRateBounds_of_geometric_clock {o : Pt X} {h : Flow X} {U P₀ ρ : STF X}
    {r₀ r₁ σ C Cb t₀ : ℝ} {Φ : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {f : ℝ → Pt X → ComplexVector n}
    (hflow : FlowStage X o h U P₀ ρ) (hjoint : JointPositiveClock X h)
    (hCharts : ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f)
    (hWindows : RicciWindows X o h ρ)
    {time : ℝ → ℝ} {s₀ a₀ b₀ hm : ℝ} {N : ℕ} (M : ℝ)
    (hclock : ClockParameter X o h ρ time s₀) (hrate : ClockRateInput o h time s₀ a₀ b₀)
    (ha₀ : 0 < a₀) (hb₀ : 0 < b₀) (hhm : 0 < hm)
    (hwindow : Real.exp (-hm * N) ≤ a₀) :
    ∃ T : ℝ, ∀ j₀, N ≤ j₀ → s₀ ≤ macroClock hm (j₀ - N) →
      T ≤ time (macroClock hm j₀) →
      let Q := sampledSpeed o h time hm
      let tk := fun k => time (gridClock Q N M hm j₀ k)
      ∀ E : Frames n, SingularFrames F tk E → (∀ k, t₀ ≤ tk k) →
        WindowRateBounds Q N M hm b₀ j₀ (rate F tk E) := by
  obtain ⟨T, _, _, hqmono, hder⟩ := hWindows.1
  refine ⟨T, ?_⟩
  intro j₀ hNj₀ hsbase hT
  dsimp only
  let Q := sampledSpeed o h time hm
  let s := gridClock Q N M hm j₀
  let tk := fun k => time (s k)
  intro E hE hlate
  have hsbase' : s₀ ≤ macroClock hm j₀ :=
    hsbase.trans ((macroClock_strictMono hm hhm).monotone (Nat.sub_le j₀ N))
  have hmacro (k : ℕ) : j₀ ≤ macroAt Q N M hm j₀ k := (macroAt_mem Q N M hm j₀ k).1
  have hs (k : ℕ) : s₀ ≤ s k := by
    exact hsbase'.trans (((macroClock_strictMono hm hhm).monotone (hmacro k)).trans
      (gridClock_mem_Ico Q N M hm hhm j₀ k).1)
  have hphysical (k : ℕ) : T ≤ tk k := by
    apply hT.trans
    exact hclock.2.1.monotoneOn hsbase' (hs k)
      (((macroClock_strictMono hm hhm).monotone (hmacro k)).trans
        (gridClock_mem_Ico Q N M hm hhm j₀ k).1)
  obtain ⟨c, hc, hclower⟩ := hrate.2.1
  intro k i _
  let j := macroAt Q N M hm j₀ k
  have hNj : N ≤ j := hNj₀.trans (hmacro k)
  have hsleft : s₀ ≤ macroClock hm (j - N) :=
    hsbase.trans ((macroClock_strictMono hm hhm).monotone (Nat.sub_le_sub_right (hmacro k) N))
  have hback := backward_macroClock_le_scaled_gridClock Q M hhm ha₀.le hwindow j₀ k hNj
  have hsmall : s₀ ≤ a₀ * s k := hsleft.trans hback
  have hlowQ : 0 < Q (j - N) := hc.trans_le (hclower _ hsleft)
  have hlowmin : b₀ * Q (j - N) ≤ ricciMin o h (tk k) := by
    exact (mul_le_mul_of_nonneg_left (hrate.1 hsleft hsmall hback) hb₀.le).trans
      (hrate.2.2.2 _ (hs k))
  constructor
  · exact hlowmin.trans (actual_rate_ge_ricciMin hflow hjoint hCharts hE hlate k
      ((mul_pos hb₀ hlowQ).trans_le hlowmin) i)
  · apply actual_rate_le_clock_bound hCharts hE hlate k _ _ i
    · intro t ht
      exact hder t ((hphysical k).trans ht.1)
    · intro t ht
      have hsend : s (k + 1) ≤ macroClock hm (j + 1) :=
        gridClock_succ_le_macro_next Q N M hm hhm j₀ k
      have hsnext : s₀ ≤ macroClock hm (j + 1) := (hs (k + 1)).trans hsend
      have htend : tk (k + 1) ≤ time (macroClock hm (j + 1)) :=
        hclock.2.1.monotoneOn (hs (k + 1)) hsnext hsend
      exact hqmono ((hphysical k).trans ht.1)
        (((hphysical k).trans ht.1).trans (ht.2.trans htend)) (ht.2.trans htend)

end Yau.Blueprint.Alignment.Y03Proof

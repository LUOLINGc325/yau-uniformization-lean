import Yau.Proofs.D05KernelBundle
import Yau.Proofs.D05EuclideanDual
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Finite-rank induction for the same generated embedded holomorphic
bundle on nested discs. Each positive-rank step spends two strict radii. -/

open Set
open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.D05Proof

theorem embedded_frame_on_smaller_disc (r : ℕ) :
    ∀ (q b : ℕ) (ρ R : ℝ)
      (B : ℂ → Submodule ℂ (EuclideanSpace ℂ (Fin q)))
      (s : Fin b → ℂ → EuclideanSpace ℂ (Fin q)),
      0 < ρ → ρ < R → LocallyProjectedOn B (Metric.ball 0 R) →
      (∀ z ∈ Metric.ball (0 : ℂ) R, Module.finrank ℂ (B z) = r) →
      (∀ i, ContDiffOn ℂ ∞ (s i) (Metric.ball 0 R)) →
      (∀ z ∈ Metric.ball (0 : ℂ) R,
        Submodule.span ℂ (Set.range fun i => s i z) = B z) →
      ∃ v : Fin r → ℂ → EuclideanSpace ℂ (Fin q),
        (∀ i, ContDiffOn ℂ ∞ (v i) (Metric.ball 0 ρ)) ∧
        ∀ z ∈ Metric.ball (0 : ℂ) ρ,
          LinearIndependent ℂ (fun i => v i z) ∧
          Submodule.span ℂ (Set.range fun i => v i z) = B z := by
  classical
  induction r with
  | zero =>
      intro q b ρ R B s hρ hρR hB hr hs hspan
      refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
      intro z hz
      have hbot : B z = ⊥ := Submodule.finrank_eq_zero.mp
        (hr z (Metric.ball_subset_ball hρR.le hz))
      exact ⟨linearIndependent_empty_type, by simp [hbot]⟩
  | succ r ih =>
      intro q b ρ R B s hρ hρR hB hr hs hspan
      have hRp : 0 < R := lt_trans hρ hρR
      have h0 : (0 : ℂ) ∈ Metric.ball 0 R := by simpa using hRp
      have hgen : ∃ i, s i 0 ≠ 0 := by
        by_contra! hzero
        have hbot : B 0 = ⊥ := by
          rw [← hspan 0 h0]
          apply le_antisymm (Submodule.span_le.mpr ?_) bot_le
          rintro _ ⟨i, rfl⟩
          simp [hzero i]
        have hdim := hr 0 h0
        rw [hbot, finrank_bot] at hdim
        omega
      obtain ⟨i, hi⟩ := hgen
      let R₁ := (2 * R + ρ) / 3
      let R₂ := (R + 2 * ρ) / 3
      have hρR₂ : ρ < R₂ := by dsimp [R₂]; linarith
      have hR₂R₁ : R₂ < R₁ := by dsimp [R₁, R₂]; linarith
      have hR₁R : R₁ < R := by dsimp [R₁]; linarith
      have hρR₁ : ρ < R₁ := lt_trans hρR₂ hR₂R₁
      have hR₂R : R₂ < R := lt_trans hR₂R₁ hR₁R
      have hR₂p : 0 < R₂ := lt_trans hρ hρR₂
      have hsiA : AnalyticOnNhd ℂ (s i) (Metric.ball 0 R) :=
        ((hs i).differentiableOn (by simp)).analyticOnNhd Metric.isOpen_ball
      have hsim : ∀ z ∈ Metric.ball (0 : ℂ) R, s i z ∈ B z := by
        intro z hz
        rw [← hspan z hz]
        exact Submodule.subset_span (Set.mem_range_self i)
      obtain ⟨e, heA, hene, hem⟩ := remove_common_zeros_in_bundle
        hR₁R hB hsiA hsim ⟨0, h0, hi⟩
      have heR : ContDiffOn ℂ ∞ e (Metric.ball 0 R) :=
        heA.contDiffOn_of_completeSpace
      have he₁ : ContDiffOn ℂ ∞ e (Metric.ball 0 R₁) :=
        heR.mono (Metric.ball_subset_ball hR₁R.le)
      obtain ⟨a, ha, hae⟩ := ambient_holomorphic_functional_of_nonvanishing
        hR₂p hR₂R₁ he₁ (fun z hz => hene z (Metric.ball_subset_closedBall hz))
      have he₂ : ContDiffOn ℂ ∞ e (Metric.ball 0 R₂) :=
        heR.mono (Metric.ball_subset_ball hR₂R.le)
      have hem₂ : ∀ z ∈ Metric.ball (0 : ℂ) R₂, e z ∈ B z :=
        fun z hz => hem z (Metric.ball_subset_ball hR₂R₁.le hz)
      let B' : ℂ → Submodule ℂ (EuclideanSpace ℂ (Fin q)) :=
        fun z => kernelPart (B z) (a z)
      let s' : Fin b → ℂ → EuclideanSpace ℂ (Fin q) :=
        fun j z => splitProjection (e z) (a z) (s j z)
      have hB₂ := hB.mono Metric.isOpen_ball (Metric.ball_subset_ball hR₂R.le)
      have hB' : LocallyProjectedOn B' (Metric.ball 0 R₂) :=
        kernelPart_locallyProjected hB₂ he₂ ha hem₂ hae
      have hr' : ∀ z ∈ Metric.ball (0 : ℂ) R₂, Module.finrank ℂ (B' z) = r := by
        intro z hz
        exact split_kernel_finrank (hem₂ z hz) (hae z hz)
          (hr z (Metric.ball_subset_ball hR₂R.le hz))
      have hs' := split_generated_bundle he₂ ha hem₂ hae
        (fun j => (hs j).mono (Metric.ball_subset_ball hR₂R.le))
        (fun z hz => hspan z (Metric.ball_subset_ball hR₂R.le hz))
      obtain ⟨v, hv, hvspan⟩ := ih q b ρ R₂ B' s' hρ hρR₂ hB' hr' hs'.1 hs'.2
      refine ⟨fun j z => (Fin.cons (e z) (fun k => v k z) :
        Fin (r + 1) → EuclideanSpace ℂ (Fin q)) j, ?_, ?_⟩
      · intro j
        refine Fin.cases ?_ (fun k => ?_) j
        · simpa only [Fin.cons_zero] using
            heR.mono (Metric.ball_subset_ball hρR.le)
        · simpa only [Fin.cons_succ] using hv k
      · intro z hz
        exact adjoin_kernel_frame
          (hem₂ z (Metric.ball_subset_ball hρR₂.le hz))
          (hae z (Metric.ball_subset_ball hρR₂.le hz))
          (hvspan z hz).1 (hvspan z hz).2

end Yau.Blueprint.D05Proof

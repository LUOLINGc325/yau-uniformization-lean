import Yau.Proofs.F01PotentialBootstrapStep
import Yau.Proofs.F01BackwardBootstrapCylinders

/-! All spatial orders retain the same actual terminal time face.
Numerical budgets precede every field; lower words alone control the
coefficient jets and no future-time margin is required. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ}

theorem backward_spatial_word_schauder_budgets (hn : 0 < n)
    {β D Ci : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hD : 1 ≤ D) (hCi : 0 ≤ Ci)
    (B : ℕ → ℝ) (hB : ∀ j, 0 < B j) :
    ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (S : Point n → Matrix (Fin n) (Fin n) ℂ) (u : Point n → ℝ) (d : Space n → ℝ),
      SchauderBound β (cylinder (ball 0 1) (-1) 0) u Ci →
      (∀ t ∈ Icc (-1 : ℝ) 0, ContDiffOn ℝ ∞ (fun z => S (z, t)) (ball 0 1)) →
      (∀ t ∈ Icc (-1 : ℝ) 0, ContDiffOn ℝ ∞ (fun z => u (z, t)) (ball 0 1)) →
      ContDiffOn ℝ ∞ d (ball 0 1) →
      (∀ j : ℕ, HolderBound β (cylinder (ball 0 1) (-1) 0)
        (fun p => iteratedFDeriv ℝ j (fun z => S (z, p.2)) p.1) (B j)) →
      (∀ j : ℕ, HolderBound β (cylinder (ball (0 : Space n) 1) (-1) 0)
        (fun p => iteratedFDeriv ℝ j d p.1) (B j)) →
      (∀ p ∈ cylinder (ball 0 1) (-1) 0, (chartPotentialMatrix S u p).PosDef) →
      (∀ p ∈ cylinder (ball 0 1) (-1) 0,
        (chartPotentialMatrix S u p - ((D⁻¹ : ℝ) : ℂ) • 1).PosSemidef ∧
        ((D : ℂ) • 1 - chartPotentialMatrix S u p).PosSemidef) →
      (∀ i : RIdx n, PotentialWordEquationsOn (cylinder (ball 0 1) (-1) 0) S u d (realVec i)) →
      ∀ (i : RIdx n) (vs : List (Space n)), NativeFrameWord vs → vs.length = k →
        SchauderBound β (backwardBootstrapCylinder n (k + 1))
          (spatialDerivativeWord vs (spatialDerivativeWord [realVec i] u)) C := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have each := fun j : Fin k => ih j.val j.isLt
    choose K hK hEst using each
    let Cu : ℝ := 1 + Ci + ∑ j : Fin k, K j
    have hSum : 0 ≤ ∑ j : Fin k, K j := Finset.sum_nonneg (fun j _ => (hK j).le)
    have hCu : 0 ≤ Cu := by dsimp only [Cu]; linarith
    have hCiCu : Ci ≤ Cu := by dsimp only [Cu]; linarith
    have hKCu (j : Fin k) : K j ≤ Cu := by
      have hh := Finset.single_le_sum (s := Finset.univ) (fun i _ => (hK i).le)
        (Finset.mem_univ j)
      dsimp only [Cu]
      linarith
    let Cs : ℝ := 1 + ∑ j : Fin (k + 2), B j.val
    have hSumS : 0 ≤ ∑ j : Fin (k + 2), B j.val :=
      Finset.sum_nonneg (fun j _ => (hB j.val).le)
    have hCs : 0 ≤ Cs := by dsimp only [Cs]; linarith
    have hBCs (j : ℕ) (hj : j ≤ k + 1) : B j ≤ Cs := by
      have hh := Finset.single_le_sum (s := Finset.univ)
        (fun i _ => (hB i.val).le) (Finset.mem_univ (⟨j, by omega⟩ : Fin (k + 2)))
      dsimp only [Cs]
      linarith
    have hb := bootstrap_buffer_data k
    obtain ⟨C, hC, hStep⟩ := potential_bootstrap_step_budget hn k
      hb.1 hb.2.1 hβ hβ1 hD hCs hCu hCi
    refine ⟨C, hC, ?_⟩
    intro S u d hInitial hSs hus hd hSj hdj hPos hBounds hEq
    have hSub := backwardBootstrapCylinder_subset_initial (n := n) k
    have hR := (bootstrapRadius_bounds k).2
    have hSspace : ball (0 : Space n) (bootstrapRadius k) ⊆ ball 0 1 := ball_subset_ball hR
    have hPrev (i : RIdx n) (ws : List (Space n)) (hws : NativeFrameWord ws)
        (hsmall : ws.length < k) :
        SchauderBound β (backwardBootstrapCylinder n k)
          (spatialDerivativeWord ws (spatialDerivativeWord [realVec i] u)) Cu := by
      let j : Fin k := ⟨ws.length, hsmall⟩
      have hh := hEst j S u d hInitial hSs hus hd hSj hdj hPos hBounds hEq i ws hws rfl
      have hRestr := backward_bootstrap_schauder_restrict (show j.val + 1 ≤ k by dsimp only [j]; omega) hh
      exact schauderBound_mono_const hRestr (hKCu j)
    have hInitialK := initial_schauder_backward_bootstrap_restrict k hInitial
    have hDD : HolderBound β (backwardBootstrapCylinder n k) (spatialDD u) Cu :=
      holderBound_mono_const hInitialK.2.2.2.1 hCiCu
    have hSField : HolderBound β (cylinder (ball 0 1) (-1) 0) S (B 0) := by
      have hh := native_frame_word_holder_of_tensor isOpen_ball
        (fun p (hp : p ∈ cylinder (ball (0 : Space n) 1) (-1) 0) => ⟨hp.1, mem_univ p.2⟩)
        (fun p hp => hSs p.2 hp.2) [] (by simp [NativeFrameWord]) (hSj 0)
      exact hh
    intro i vs hvs hlen
    have hWordEq := potentialWordEquations_backward_bootstrap_restrict (hEq i) k vs
    apply hStep (bootstrapRadius k) (bootstrapRadius (k + 1))
      (-bootstrapRadius k) 0 (-bootstrapRadius (k + 1)) 0 S u d
      (show -bootstrapRadius (k + 1) < (0 : ℝ) by linarith [(bootstrapRadius_bounds (k + 1)).1])
      hb.2.2.1 hb.2.2.2.1 le_rfl
    · exact holderBound_mono_const (holderBound_restrict hSField hSub) (hBCs 0 (by omega))
    · intro p hp
      exact (hSs p.2 (hSub hp).2).mono hSspace
    · intro p hp
      exact (hus p.2 (hSub hp).2).mono hSspace
    · exact hd.mono hSspace
    · intro j hj
      exact holderBound_mono_const (holderBound_restrict (hSj j) hSub) (hBCs j hj)
    · intro j hj
      exact holderBound_mono_const (holderBound_restrict (hdj j) hSub) (hBCs j hj)
    · exact fun p hp => hPos p (hSub hp)
    · exact fun p hp => hBounds p (hSub hp)
    · exact hInitialK
    · exact hDD
    · exact hPrev
    · exact hvs
    · exact hlen
    · exact hWordEq.1
    · exact hWordEq.2

end Yau.NodeProofs.F01Aux

import Yau.LeafProofs.L10InteriorExact

/-! The same smooth harmonic function has uniform bounds at every order,
using the accepted L10 and L09 estimates on fixed nested balls. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs

theorem smooth_iterated_derivative_sq_integrable_ball {n : ℕ}
    {u : ComplexVector n → ℂ} (hu : ContDiff ℝ ∞ u) (j : ℕ) (r : ℝ) :
    IntegrableOn (fun z => ‖iteratedFDeriv ℝ j u z‖ ^ 2)
      (Metric.ball 0 r) (lebesgueC n) := by
  rw [lebesgueC_eq_volume]
  have hc : Continuous (iteratedFDeriv ℝ j u) :=
    continuous_iff_continuousAt.mpr fun x => hu.contDiffAt.continuousAt_iteratedFDeriv (by simp)
  exact ((hc.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall 0 r)).mono_set
    Metric.ball_subset_closedBall

theorem iterated_derivative_eq_zero_on_open {n : ℕ} {f : ComplexVector n → ℂ}
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hf : Set.EqOn f 0 O)
    (j : ℕ) {z : ComplexVector n} (hz : z ∈ O) : iteratedFDeriv ℝ j f z = 0 := by
  have he : f =ᶠ[𝓝 z] (0 : ComplexVector n → ℂ) := by
    filter_upwards [hO.mem_nhds hz] with x hx
    exact hf hx
  simpa using (he.iteratedFDeriv ℝ j).self_of_nhds

theorem sobolevNormSq_eq_zero_on_open {n : ℕ} {f : ComplexVector n → ℂ}
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hf : Set.EqOn f 0 O) (s : ℕ) :
    LeafCandidates.sobolevNormSq O f s = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem hO.measurableSet] with z hz
  simp [iterated_derivative_eq_zero_on_open hO hf j hz]

theorem exists_harmonic_derivative_bounds (n : ℕ) (ell U : ℝ)
    (hell : 0 < ell) (hU : 0 ≤ U) (A : ℕ → ℝ) (hA : ∀ s, 0 < A s) :
    ∃ D : ℕ → ℝ, (∀ j, 0 < D j) ∧
      ∀ (a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
        (b : ComplexVector n → RIdx n → ℝ),
        (∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) (Metric.ball 0 (3 / 8 : ℝ))) →
        (∀ i, ContDiffOn ℝ ∞ (fun z => b z i) (Metric.ball 0 (3 / 8 : ℝ))) →
        (∀ z ∈ Metric.ball 0 (3 / 8 : ℝ), (a z).IsSymm ∧
          ∀ v : RIdx n → ℝ, ell * ∑ i, v i ^ 2 ≤ ∑ i, ∑ j, a z i j * v i * v j) →
        (∀ s k, k ≤ s + 1 → ∀ z ∈ Metric.ball 0 (3 / 8 : ℝ), ∀ i j,
          ‖iteratedFDeriv ℝ k (fun w => a w i j) z‖ ≤ A s ∧
          ‖iteratedFDeriv ℝ k (fun w => b w i) z‖ ≤ A s) →
        ∀ u : ComplexVector n → ℂ, ContDiff ℝ ∞ u →
          LeafCandidates.sobolevNormSq (Metric.ball 0 (3 / 8 : ℝ)) u 0 ≤ U →
          Set.EqOn (LeafCandidates.ellipticOp a b u) 0 (Metric.ball 0 (3 / 8 : ℝ)) →
          ∀ j z, z ∈ Metric.ball (0 : ComplexVector n) (1 / 4 : ℝ) →
            ‖iteratedFDeriv ℝ j u z‖ ≤ D j := by
  classical
  have he (j : ℕ) := interiorEllipticEstimate n (j + n + 1)
    (1 / 3) (3 / 8) ell (A (j + n + 1)) (by norm_num) (by norm_num) hell (hA _)
  have hs (j : ℕ) := interiorSobolevEmbedding n j ((j + n + 1) + 2)
    (by omega) (1 / 4) (1 / 3) (by norm_num) (by norm_num)
  let Ce := fun j => (he j).choose
  let Cs := fun j => (hs j).choose
  have hCe (j : ℕ) : 0 < Ce j := (he j).choose_spec.1
  have hCs (j : ℕ) : 0 < Cs j := (hs j).choose_spec.1
  refine ⟨fun j => 1 + Ce j * Cs j * Real.sqrt U, fun j => by
    have hc₁ := hCe j
    have hc₂ := hCs j
    positivity, ?_⟩
  intro a b ha hb helliptic hcoeff u hu hmass hzero j z hz
  have hFint (k : ℕ) :
      IntegrableOn (fun z => ‖iteratedFDeriv ℝ k (LeafCandidates.ellipticOp a b u) z‖ ^ 2)
        (Metric.ball 0 (3 / 8 : ℝ)) (lebesgueC n) := by
    apply (integrableOn_zero : IntegrableOn (fun _ : ComplexVector n => (0 : ℝ))
      (Metric.ball 0 (3 / 8 : ℝ)) (lebesgueC n)).congr_fun
    · intro x hx
      change (0 : ℝ) = ‖iteratedFDeriv ℝ k (LeafCandidates.ellipticOp a b u) x‖ ^ 2
      rw [iterated_derivative_eq_zero_on_open Metric.isOpen_ball hzero k hx]
      simp
    · exact measurableSet_ball
  have hE := (he j).choose_spec.2 a b ha hb helliptic (hcoeff (j + n + 1)) u hu.contDiffOn
    (fun k _ => smooth_iterated_derivative_sq_integrable_ball hu k (3 / 8))
    (fun k _ => hFint k)
  rw [sobolevNormSq_eq_zero_on_open Metric.isOpen_ball hzero,
    Real.sqrt_zero, add_zero] at hE
  have hS := (hs j).choose_spec.2 u hu.contDiffOn
    (fun k _ => smooth_iterated_derivative_sq_integrable_ball hu k (1 / 3)) z hz
  calc
    ‖iteratedFDeriv ℝ j u z‖ ≤ Cs j * Real.sqrt
        (LeafCandidates.sobolevNormSq (Metric.ball 0 (1 / 3 : ℝ)) u ((j + n + 1) + 2)) := hS
    _ ≤ Cs j * (Ce j * Real.sqrt
        (LeafCandidates.sobolevNormSq (Metric.ball 0 (3 / 8 : ℝ)) u 0)) :=
      mul_le_mul_of_nonneg_left hE (hCs j).le
    _ ≤ Cs j * (Ce j * Real.sqrt U) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmass) (hCe j).le) (hCs j).le
    _ ≤ 1 + Ce j * Cs j * Real.sqrt U := by nlinarith

end Yau.Proofs.C04ChartsAux

import Yau.Proofs.V02FlowEuclidean
import Mathlib.Data.Fin.Tuple.Basic

/-! Finite ordered compositions, including the empty family and exact single-time slices. -/

open scoped Topology ContDiff
open Metric

noncomputable section
namespace Yau.Blueprint.V02FlowProof

def finiteFlowCompose {Y : Type*} : (b : ℕ) →
    (Fin b → ℂ × Y → Y) → Y × (Fin b → ℂ) → Y
  | 0, _, p => p.1
  | b + 1, F, p => finiteFlowCompose b (fun k => F k.succ)
      (F 0 (p.2 0, p.1), fun k => p.2 k.succ)

theorem finiteFlowCompose_zero {Y : Type*} (b : ℕ) (F : Fin b → ℂ × Y → Y)
    (hzero : ∀ k y, F k (0, y) = y) (y : Y) : finiteFlowCompose b F (y, 0) = y := by
  induction b with
  | zero => rfl
  | succ b ih =>
    simp only [finiteFlowCompose, Pi.zero_apply, hzero]
    exact ih (fun k => F k.succ) (fun k y => hzero k.succ y)

theorem finiteFlowCompose_single {Y : Type*} (b : ℕ) (F : Fin b → ℂ × Y → Y)
    (hzero : ∀ k y, F k (0, y) = y) (y : Y) (k : Fin b) (z : ℂ) :
    finiteFlowCompose b F (y, Pi.single k z) = F k (z, y) := by
  classical
  induction b with
  | zero => exact Fin.elim0 k
  | succ b ih =>
    refine Fin.cases ?_ (fun k => ?_) k
    · have htail : (fun j : Fin b =>
          (Pi.single (0 : Fin (b + 1)) z : Fin (b + 1) → ℂ) j.succ) = 0 := by
        funext j
        simp [Pi.single_apply, Fin.succ_ne_zero]
      simp only [finiteFlowCompose, Pi.single_eq_same, htail]
      exact finiteFlowCompose_zero b (fun j => F j.succ) (fun j y => hzero j.succ y) _
    · have hhead : (Pi.single k.succ z : Fin (b + 1) → ℂ) (0 : Fin (b + 1)) = 0 := by
        simp [Pi.single_apply, Fin.succ_ne_zero, Ne.symm (Fin.succ_ne_zero k)]
      have htail : (fun j : Fin b =>
          (Pi.single k.succ z : Fin (b + 1) → ℂ) j.succ) = Pi.single k z := by
        funext j
        simp only [Pi.single_apply, Fin.succ_inj]
      simp only [finiteFlowCompose, hhead, hzero, htail]
      exact ih (fun j => F j.succ) (fun j y => hzero j.succ y) k

theorem finiteFlowCompose_displacement
    {V : Type*} [PseudoMetricSpace V] (b : ℕ) (F : Fin b → ℂ × V → V)
    {a u : V} {d ρ A : ℝ} {τ : Fin b → ℂ} (hρ : 0 ≤ ρ) (hA : 0 ≤ A)
    (hτ : ∀ k, ‖τ k‖ ≤ ρ)
    (hstep : ∀ k t x, ‖t‖ ≤ ρ → x ∈ ball a d → dist (F k (t, x)) x ≤ ρ * A)
    (hbudget : dist u a + (b : ℝ) * ρ * A < d) :
    dist (finiteFlowCompose b F (u, τ)) u ≤ (b : ℝ) * ρ * A := by
  induction b generalizing u with
  | zero => simp [finiteFlowCompose]
  | succ b ih =>
    have hu : u ∈ ball a d := mem_ball.mpr
      (lt_of_le_of_lt (le_add_of_nonneg_right (by positivity)) hbudget)
    have hfirst := hstep 0 (τ 0) u (hτ 0) hu
    have hnext : dist (F 0 (τ 0, u)) a + (b : ℝ) * ρ * A < d := by
      have htri := dist_triangle (F 0 (τ 0, u)) u a
      push_cast at hbudget
      nlinarith
    have htail := ih (fun k => F k.succ) (fun k => hτ k.succ)
      (fun k => hstep k.succ) hnext
    calc
      dist (finiteFlowCompose (b + 1) F (u, τ)) u ≤
          dist (finiteFlowCompose b (fun k => F k.succ)
            (F 0 (τ 0, u), fun k => τ k.succ)) (F 0 (τ 0, u)) +
            dist (F 0 (τ 0, u)) u := dist_triangle _ _ _
      _ ≤ (b : ℝ) * ρ * A + ρ * A := add_le_add htail hfirst
      _ = ((b + 1 : ℕ) : ℝ) * ρ * A := by push_cast; ring

theorem finiteFlowCompose_contDiffAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (b : ℕ) (F : Fin b → ℂ × V → V) {a u : V} {d T ρ A : ℝ}
    {τ : Fin b → ℂ} (hρ : 0 ≤ ρ) (hA : 0 ≤ A)
    (hτ : ∀ k, ‖τ k‖ ≤ ρ) (hτT : ∀ k, τ k ∈ ball (0 : ℂ) T)
    (hF : ∀ k, ContDiffOn ℂ ∞ (F k) (ball (0 : ℂ) T ×ˢ ball a d))
    (hstep : ∀ k t x, ‖t‖ ≤ ρ → x ∈ ball a d → dist (F k (t, x)) x ≤ ρ * A)
    (hbudget : dist u a + (b : ℝ) * ρ * A < d) :
    ContDiffAt ℂ ∞ (finiteFlowCompose b F) (u, τ) := by
  induction b generalizing u with
  | zero => exact contDiffAt_fst
  | succ b ih =>
    have hu : u ∈ ball a d := mem_ball.mpr
      (lt_of_le_of_lt (le_add_of_nonneg_right (by positivity)) hbudget)
    have hfirst := hstep 0 (τ 0) u (hτ 0) hu
    have hnext : dist (F 0 (τ 0, u)) a + (b : ℝ) * ρ * A < d := by
      have htri := dist_triangle (F 0 (τ 0, u)) u a
      push_cast at hbudget
      nlinarith
    have hi := ih (fun k => F k.succ) (fun k => hτ k.succ) (fun k => hτT k.succ)
      (fun k => hF k.succ) (fun k => hstep k.succ) hnext
    have htime : ContDiff ℂ ∞ (fun p : V × (Fin (b + 1) → ℂ) => p.2 0) :=
      (contDiff_apply ℂ (fun _ : Fin (b + 1) => ℂ) 0).comp contDiff_snd
    have htail : ContDiff ℂ ∞ (fun p : V × (Fin (b + 1) → ℂ) =>
        fun k : Fin b => p.2 k.succ) := contDiff_pi.mpr fun k =>
      (contDiff_apply ℂ (fun _ : Fin (b + 1) => ℂ) k.succ).comp contDiff_snd
    have hfirstSmooth : ContDiffAt ℂ ∞ (F 0) (τ 0, u) := (hF 0).contDiffAt
      ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨hτT 0, hu⟩)
    exact hi.comp (u, τ)
      ((hfirstSmooth.comp (u, τ) (htime.contDiffAt.prodMk contDiffAt_fst)).prodMk htail.contDiffAt)

end Yau.Blueprint.V02FlowProof

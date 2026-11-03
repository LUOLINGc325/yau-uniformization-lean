import Yau.Proofs.U02TailShadowing
import Yau.Proofs.U02TailAlgebra

/-! Construct the original full-prefix local limit from U01. Reindexing
never changes the original polynomial sequence, clock, or error exponent. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.NodeProofs.U02Proof

open Yau Blueprint

theorem backwardShadowing_local_limit {n m : ℕ} (hU01 : BackwardShadowing n m)
    {Omega : Set (ComplexVector m)} {s : ℕ → ℝ} {G Ginv : ℕ → PolyMap n}
    {zeta : ℕ → ComplexVector m → ComplexVector n} {nu delta : ℝ}
    (hOmega : IsOpen Omega) (hnu : 0 < nu) (hnu1 : nu < 1 / 10)
    (hdelta : 0 < delta) (hdelta1 : delta < 1 / 10)
    (hs : Tendsto s atTop atTop)
    (hstep : ∀ᶠ k in atTop, 1 ≤ s (k + 1) - s k ∧ s (k + 1) ≤ (1 + delta) * s k)
    (hauto : ∀ k, IsPolyAutomorphism (G k) (Ginv k))
    (hprefix : ∀ k, IsPolyAutomorphism (forwardComp G k) (backwardComp Ginv k))
    (hdiff : ∀ᶠ k in atTop, DifferentiableOn ℂ (zeta k) Omega)
    (horbit : ∀ᶠ k in atTop, ∀ z ∈ Omega,
      ‖zeta k z‖ ≤ Real.exp (-2 * nu * s k) ∧
      ‖zeta (k + 1) z - (G k).eval (zeta k z)‖ ≤ Real.exp (-10 * s k))
    (hinv : ∀ᶠ k in atTop, ∀ u v : ComplexVector n,
      ‖u‖ < Real.exp (-nu * s (k + 1)) → ‖v‖ < Real.exp (-nu * s (k + 1)) →
      ‖(Ginv k).eval u - (Ginv k).eval v‖ ≤
        Real.exp (s (k + 1) - s k) * ‖u - v‖) :
    ∃ psi : ComplexVector m → ComplexVector n,
      DifferentiableOn ℂ psi Omega ∧
      (∀ K ⊆ Omega, IsCompact K → TendstoUniformlyOn
        (fun l z => (backwardComp Ginv l).eval (zeta l z)) psi atTop K) ∧
      ∀ᶠ k in atTop, ∀ z ∈ Omega,
        ‖(forwardComp G k).eval (psi z) - zeta k z‖ ≤ Real.exp (-6 * s k) := by
  obtain ⟨N, xi, hfirst, _htubes⟩ := backwardShadowing_on_tail hU01
    hOmega hnu hnu1 hdelta hdelta1 hs hstep hauto hdiff horbit hinv
  obtain ⟨a, ha⟩ := eventually_atTop.1 hfirst
  let Q := backwardComp Ginv (a + N)
  let psi := fun z => Q.eval (xi a z)
  have hpsi : DifferentiableOn ℂ psi Omega :=
    ((polynomial_contDiff Q).differentiable (by simp)).comp_differentiableOn (ha a le_rfl).1
  have hfull : ∀ K ⊆ Omega, IsCompact K → TendstoUniformlyOn
      (fun l z => (backwardComp Ginv l).eval (zeta l z)) psi atTop K := by
    intro K hKO hK
    have hc := polynomial_uniform_compact_limit hK
      ((ha a le_rfl).1.continuousOn.mono hKO)
      ((ha a le_rfl).2.1 K hKO hK) Q
    have hc' : TendstoUniformlyOn
        (fun l z => (backwardComp Ginv (l + N)).eval (zeta (l + N) z)) psi atTop K := by
      apply hc.congr
      refine eventually_atTop.2 ⟨a, ?_⟩
      intro l hl z hz
      exact (backwardComp_tail_eval Ginv N a l hl (zeta (l + N) z)).symm
    exact (tendstoUniformlyOn_nat_add_iff N).mp hc'
  have hpoint : ∀ z ∈ Omega,
      Tendsto (fun l => (backwardComp Ginv l).eval (zeta l z)) atTop (𝓝 (psi z)) := by
    intro z hz
    exact (hfull {z} (by simpa using hz) isCompact_singleton).tendsto_at (by simp)
  refine ⟨psi, hpsi, hfull, eventually_atTop.2 ⟨a + N, ?_⟩⟩
  intro k hk z hz
  let j := k - N
  have hja : a ≤ j := by dsimp [j]; omega
  have hjk : j + N = k := by dsimp [j]; omega
  have hxi := ((ha j hja).2.1 {z} (by simpa using hz) isCompact_singleton).tendsto_at
    (by simp : z ∈ ({z} : Set (ComplexVector m)))
  have hpsiLimit := ((polynomial_contDiff (forwardComp G k)).continuous.tendsto (psi z)).comp
    (hpoint z hz)
  have hpsiTail := hpsiLimit.comp (tendsto_add_atTop_nat N)
  have hident : ∀ᶠ l in atTop,
      (forwardComp G k).eval ((backwardComp Ginv (l + N)).eval (zeta (l + N) z)) =
        (backwardSegment (fun i => Ginv (i + N)) j (l - j)).eval (zeta (l + N) z) := by
    refine eventually_atTop.2 ⟨j, ?_⟩
    intro l hl
    rw [backwardComp_tail_eval Ginv N j l hl, hjk,
      forward_backward_eval_cancel (hprefix k)]
  have hpsiTail' := hpsiTail.congr' hident
  have heq := tendsto_nhds_unique hpsiTail' hxi
  rw [heq]
  simpa only [hjk] using ((ha j hja).2.2 z hz).1

end Yau.NodeProofs.U02Proof

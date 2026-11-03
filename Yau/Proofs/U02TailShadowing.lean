import Yau.Blueprint.Nodes

/-! Apply the original U01 contract after all four eventual local estimates
have entered their proved range. The same finite polynomial prefix is retained. -/

open scoped Topology
open Filter

namespace Yau.NodeProofs.U02Proof

open Yau Blueprint

theorem backwardShadowing_on_tail {n m : ℕ} (hU01 : BackwardShadowing n m)
    {Omega : Set (ComplexVector m)} {s : ℕ → ℝ} {G Ginv : ℕ → PolyMap n}
    {zeta : ℕ → ComplexVector m → ComplexVector n} {nu delta : ℝ}
    (hOmega : IsOpen Omega) (hnu : 0 < nu) (hnu1 : nu < 1 / 10)
    (hdelta : 0 < delta) (hdelta1 : delta < 1 / 10)
    (hs : Tendsto s atTop atTop)
    (hstep : ∀ᶠ k in atTop, 1 ≤ s (k + 1) - s k ∧ s (k + 1) ≤ (1 + delta) * s k)
    (hauto : ∀ k, IsPolyAutomorphism (G k) (Ginv k))
    (hdiff : ∀ᶠ k in atTop, DifferentiableOn ℂ (zeta k) Omega)
    (horbit : ∀ᶠ k in atTop, ∀ z ∈ Omega,
      ‖zeta k z‖ ≤ Real.exp (-2 * nu * s k) ∧
      ‖zeta (k + 1) z - (G k).eval (zeta k z)‖ ≤ Real.exp (-10 * s k))
    (hinv : ∀ᶠ k in atTop, ∀ u v : ComplexVector n,
      ‖u‖ < Real.exp (-nu * s (k + 1)) → ‖v‖ < Real.exp (-nu * s (k + 1)) →
      ‖(Ginv k).eval u - (Ginv k).eval v‖ ≤
        Real.exp (s (k + 1) - s k) * ‖u - v‖) :
    ∃ N : ℕ,
      let st := fun k => s (k + N)
      let Gt := fun k => G (k + N)
      let Git := fun k => Ginv (k + N)
      let zt := fun k => zeta (k + N)
      ∃ xi : ℕ → ComplexVector m → ComplexVector n,
        (∀ᶠ k in atTop, DifferentiableOn ℂ (xi k) Omega ∧
          (∀ K ⊆ Omega, IsCompact K →
            TendstoUniformlyOn
              (fun l z => (backwardSegment Git k (l - k)).eval (zt l z)) (xi k) atTop K) ∧
          (∀ z ∈ Omega, ‖xi k z - zt k z‖ ≤ Real.exp (-6 * st k) ∧
            xi (k + 1) z = (Gt k).eval (xi k z))) ∧
        (∀ᶠ k in atTop, ∀ l, k ≤ l → ∀ i, k ≤ i → i < l → ∀ z ∈ Omega,
          ‖(backwardSegment Git (i + 1) (l - (i + 1))).eval (zt l z)‖ <
            Real.exp (-nu * st (i + 1)) ∧
          ‖(Gt i).eval (zt i z)‖ < Real.exp (-nu * st (i + 1))) := by
  have hall : ∀ᶠ k in atTop,
      (1 ≤ s (k + 1) - s k ∧ s (k + 1) ≤ (1 + delta) * s k) ∧
      DifferentiableOn ℂ (zeta k) Omega ∧
      (∀ z ∈ Omega, ‖zeta k z‖ ≤ Real.exp (-2 * nu * s k) ∧
        ‖zeta (k + 1) z - (G k).eval (zeta k z)‖ ≤ Real.exp (-10 * s k)) ∧
      (∀ u v : ComplexVector n,
        ‖u‖ < Real.exp (-nu * s (k + 1)) → ‖v‖ < Real.exp (-nu * s (k + 1)) →
        ‖(Ginv k).eval u - (Ginv k).eval v‖ ≤
          Real.exp (s (k + 1) - s k) * ‖u - v‖) := by
    filter_upwards [hstep, hdiff, horbit, hinv] with k h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 hall
  refine ⟨N, ?_⟩
  apply hU01 Omega (fun k => s (k + N)) (fun k => G (k + N))
    (fun k => Ginv (k + N)) (fun k => zeta (k + N)) nu delta
    hOmega hnu hnu1 hdelta hdelta1 (hs.comp (tendsto_add_atTop_nat N))
  · intro k
    simpa only [Nat.add_right_comm k 1 N] using (hN (k + N) (by omega)).1
  · intro k
    exact hauto (k + N)
  · intro k
    exact (hN (k + N) (by omega)).2.1
  · apply Eventually.of_forall
    intro k
    simpa only [Nat.add_right_comm k 1 N] using (hN (k + N) (by omega)).2.2.1
  · apply Eventually.of_forall
    intro k
    simpa only [Nat.add_right_comm k 1 N] using (hN (k + N) (by omega)).2.2.2

end Yau.NodeProofs.U02Proof

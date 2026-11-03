import Yau.Proofs.U01Finite
import Yau.Proofs.U02TailAlgebra
import Yau.Proofs.U02InverseTube

/-! Finite backward control is uniform in every sufficiently late starting
index. This uses the proved U01 finite-error lemma on the actual tail. -/

open scoped Topology
open Filter

noncomputable section
namespace Yau.NodeProofs.U02Proof
open Yau Blueprint

theorem finite_shadow_on_late_tails {n m : ℕ} {s : ℕ → ℝ}
    {G Ginv : ℕ → PolyMap n} {Omega : ℕ → Set (ComplexVector m)}
    {zeta : ℕ → ℕ → ComplexVector m → ComplexVector n} {nu delta : ℝ}
    (hnu : 0 < nu) (hnu1 : nu < 1 / 10) (hdelta : delta < 1 / 10)
    (hs : Tendsto s atTop atTop)
    (hstep : ∀ᶠ k in atTop, 1 ≤ s (k + 1) - s k ∧ s (k + 1) ≤ (1 + delta) * s k)
    (hauto : ∀ k, IsPolyAutomorphism (G k) (Ginv k))
    (horbit : ∀ᶠ a in atTop, ∀ k, a ≤ k → ∀ z ∈ Omega a,
      ‖zeta a k z‖ ≤ Real.exp (-2 * nu * s k) ∧
      ‖zeta a (k + 1) z - (G k).eval (zeta a k z)‖ ≤ Real.exp (-10 * s k))
    (hinv : ∀ᶠ k in atTop, ∀ u v : ComplexVector n,
      ‖u‖ < Real.exp (-nu * s (k + 1)) → ‖v‖ < Real.exp (-nu * s (k + 1)) →
      ‖(Ginv k).eval u - (Ginv k).eval v‖ ≤ Real.exp (s (k + 1) - s k) * ‖u - v‖) :
    ∀ᶠ a in atTop, ∀ l, a ≤ l → ∀ z ∈ Omega a,
      ‖(backwardSegment Ginv a (l - a)).eval (zeta a l z) - zeta a a z‖ ≤
        Real.exp (-7 * s a) := by
  have hall : ∀ᶠ k in atTop,
      (1 ≤ s (k + 1) - s k ∧ s (k + 1) ≤ (1 + delta) * s k) ∧
      1 ≤ s k ∧ Real.exp (-nu * s k) < 1 / 2 ∧
      ∀ u v : ComplexVector n,
        ‖u‖ < Real.exp (-nu * s (k + 1)) → ‖v‖ < Real.exp (-nu * s (k + 1)) →
        ‖(Ginv k).eval u - (Ginv k).eval v‖ ≤ Real.exp (s (k + 1) - s k) * ‖u - v‖ := by
    filter_upwards [hstep, (tendsto_atTop.1 hs) 1,
      eventually_exp_decay_lt hs hnu (by norm_num : (0 : ℝ) < 1 / 2), hinv]
      with k h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 hall
  filter_upwards [horbit, eventually_ge_atTop N] with a horba ha
  intro l hal z hz
  have hh := U01Proof.finite_error (K := 0)
    (s := fun k => s (k + a)) (G := fun k => G (k + a))
    (Ginv := fun k => Ginv (k + a)) (zeta := fun k => zeta a (k + a))
    (Ω := Omega a) hnu hnu1 hdelta
    (fun k => by simpa only [Nat.add_right_comm k 1 a] using (hN (k + a) (by omega)).1)
    (fun k _ => (hN (k + a) (by omega)).2.1)
    (fun k _ => (hN (k + a) (by omega)).2.2.1)
    (fun k => hauto (k + a))
    (fun k _ => by simpa only [Nat.add_right_comm k 1 a] using horba (k + a) (by omega))
    (fun k _ => by simpa only [Nat.add_right_comm k 1 a] using (hN (k + a) (by omega)).2.2.2)
    (l - a) 0 (by omega) z hz
  simpa only [U01Proof.approx, backwardSegment_shift, Nat.zero_add,
    Nat.sub_add_cancel hal] using hh

end Yau.NodeProofs.U02Proof

import Yau.Proofs.V04PenaltyLimits

/-! Finite sums and the ordered sequential-then-epsilon upper limit.
No bounded-branch limsup or exchange of limits is used. -/

open Filter
open scoped Topology
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

theorem seqUpperZero_sum {ι : Type*} [Fintype ι] (a : ι → ℕ → ℝ)
    (ha : ∀ i, SeqUpperZero (a i)) : SeqUpperZero (fun ν => ∑ i, a i ν) := by
  intro r hr
  let s : ℝ := r / (Fintype.card ι + 1)
  have hs : 0 < s := div_pos hr (by positivity)
  have hall : ∀ᶠ ν in atTop, ∀ i, a i ν ≤ s := eventually_all.mpr (fun i => ha i s hs)
  filter_upwards [hall] with ν hν
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hν i)
  have hsr : (Fintype.card ι : ℝ) * s ≤ r := by
    have heq : ((Fintype.card ι : ℝ) + 1) * s = r := by
      dsimp [s]
      field_simp
    nlinarith only [heq, hs.le]
  exact hh.trans (by simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hsr)

theorem seqUpperZero_mono {a b : ℕ → ℝ} (hb : SeqUpperZero b) (h : ∀ ν, a ν ≤ b ν) :
    SeqUpperZero a := by
  intro r hr
  filter_upwards [hb r hr] with ν hν
  exact (h ν).trans hν

theorem epsSeqZero_of_nonneg_upper (x : ℝ → ℕ → ℝ) (R : ℝ → ℝ)
    (hx : ∀ ε ν, 0 ≤ x ε ν) (hR : Tendsto R (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hupper : ∀ᶠ ε in 𝓝[>] (0 : ℝ), SeqUpperZero (fun ν => x ε ν - R ε)) :
    EpsSeqZero x := by
  intro r hr
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), |R ε| < r / 2 := by
    have hh := hR.eventually (Metric.ball_mem_nhds (0 : ℝ) (half_pos hr))
    filter_upwards [hh] with ε hε
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hε
  filter_upwards [hupper, hsmall] with ε hε hRε
  filter_upwards [hε (r / 2) (half_pos hr)] with ν hν
  rw [abs_of_nonneg (hx ε ν)]
  have hh := le_abs_self (R ε)
  linarith only [hν, hRε, hh]

end Yau.Blueprint.V04Proof

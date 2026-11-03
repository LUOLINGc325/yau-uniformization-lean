import Yau.Proofs.P07ScaledFamily
import Yau.LeafProofs.L12
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! The dyadic series is locally one active smooth summand, including
points on dyadic boundaries through the family's genuine local plateaux. -/
noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace Yau.NodeProofs.P07Aux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

def dyadicExhaustion (v : ℝ → M.Carrier → ℝ) (x : M.Carrier) : ℝ :=
  1 + ∑' j : ℕ, (2 : ℝ) ^ j * v ((2 : ℝ) ^ j) x

theorem dyadic_geometric_sum (k : ℕ) : ∑ j ∈ Finset.range k, (2 : ℝ) ^ j = (2 : ℝ) ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

theorem dyadic_local_formula {g : SmoothMetric M} {o : M.Carrier}
    {v : ℝ → M.Carrier → ℝ} {D1 D2 : ℝ} (hv : ScaledCutoffFamily g o v D1 D2)
    (x : M.Carrier) (k : ℕ) (hupper : distFrom g.form o x < (2 : ℝ) ^ (k + 1))
    (hlower : k = 0 ∨ (2 : ℝ) ^ k ≤ distFrom g.form o x) :
    dyadicExhaustion v =ᶠ[𝓝 x] fun y => (2 : ℝ) ^ k * (1 + v ((2 : ℝ) ^ k) y) := by
  have hlow : ∀ᶠ y in 𝓝 x, ∀ j ∈ Finset.range k, v ((2 : ℝ) ^ j) y = 1 := by
    apply (Filter.eventually_all_finset (Finset.range k)).mpr
    intro j hj
    apply ((hv ((2 : ℝ) ^ j) (by positivity)).2 x).2.2.1
    have hjk : j + 1 ≤ k := Finset.mem_range.mp hj
    have hpow : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hjk
    have hl : (2 : ℝ) ^ k ≤ distFrom g.form o x := by
      rcases hlower with hk | hk
      · subst k
        simp at hj
      · exact hk
    rw [pow_succ] at hpow
    linarith
  have htail : ∀ᶠ y in 𝓝 x, ∀ j ∉ Finset.range (k + 1),
      (2 : ℝ) ^ j * v ((2 : ℝ) ^ j) y = 0 := by
    filter_upwards [(continuous_distFrom g o).continuousAt.eventually (Iio_mem_nhds hupper)] with y hy j hj
    have hpow : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ j :=
      pow_le_pow_right₀ (by norm_num) (Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h)))
    rw [scaledCutoff_zero hv (by positivity) y (hy.le.trans hpow), mul_zero]
  filter_upwards [hlow, htail] with y hly hty
  change 1 + ∑' j : ℕ, (2 : ℝ) ^ j * v ((2 : ℝ) ^ j) y = _
  rw [tsum_eq_sum hty, Finset.sum_range_succ]
  have hs : ∑ j ∈ Finset.range k, (2 : ℝ) ^ j * v ((2 : ℝ) ^ j) y = (2 : ℝ) ^ k - 1 := by
    calc
      _ = ∑ j ∈ Finset.range k, (2 : ℝ) ^ j := Finset.sum_congr rfl (fun j hj => by rw [hly j hj, mul_one])
      _ = _ := dyadic_geometric_sum k
  rw [hs]
  ring

theorem dyadic_exists_local_formula {g : SmoothMetric M} {o : M.Carrier}
    {v : ℝ → M.Carrier → ℝ} {D1 D2 : ℝ} (hv : ScaledCutoffFamily g o v D1 D2)
    (x : M.Carrier) : ∃ k : ℕ,
      (k = 0 ∨ (2 : ℝ) ^ k ≤ distFrom g.form o x) ∧
      distFrom g.form o x < 2 * (2 : ℝ) ^ k ∧
      dyadicExhaustion v =ᶠ[𝓝 x] fun y => (2 : ℝ) ^ k * (1 + v ((2 : ℝ) ^ k) y) := by
  by_cases hx : distFrom g.form o x < 1
  · refine ⟨0, Or.inl rfl, by norm_num; linarith, ?_⟩
    apply dyadic_local_formula hv x 0 (by norm_num; linarith) (Or.inl rfl)
  · obtain ⟨k, hklo, hkhi⟩ := exists_nat_pow_near (le_of_not_gt hx) (by norm_num : (1 : ℝ) < 2)
    refine ⟨k, Or.inr hklo, by simpa [pow_succ, mul_comm] using hkhi, ?_⟩
    exact dyadic_local_formula hv x k hkhi (Or.inr hklo)

end Yau.NodeProofs.P07Aux

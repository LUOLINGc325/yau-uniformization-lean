import Yau.Proofs.F04SeeleyMoments
import Yau.Proofs.F04SeeleyTailBound

open Filter
open scoped Topology

noncomputable section

namespace Yau.F04Proof.Seeley

def leftWeight (k : ℕ) : ℝ := ∏ j ∈ Finset.range k,
  (1 + dyadic j) / (dyadic k - dyadic j)

theorem leftWeight_pos (k : ℕ) : 0 < leftWeight k := by
  apply Finset.prod_pos
  intro j hj
  exact div_pos (by linarith [dyadic_pos j])
    (sub_pos.mpr (dyadic_strictMono (Finset.mem_range.mp hj)))

theorem finiteWeight_factor (N k : ℕ) (hk : k ≤ N) :
    finiteWeight N k = (-1 : ℝ) ^ k * leftWeight k * tailWeight k (N - k) := by
  have hs : (Finset.range (N + 1)).erase k =
      Finset.range k ∪ Finset.Ico (k + 1) (N + 1) := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdis : Disjoint (Finset.range k) (Finset.Ico (k + 1) (N + 1)) := by
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    simp only [Finset.mem_range, Finset.mem_Ico] at hj hj'
    omega
  rw [finiteWeight, ite_eq_left hk, hs, Finset.prod_union hdis]
  have hleft : (∏ j ∈ Finset.range k,
      (1 + dyadic j) / (dyadic j - dyadic k)) = (-1 : ℝ) ^ k * leftWeight k := by
    calc
      _ = ∏ j ∈ Finset.range k, -((1 + dyadic j) / (dyadic k - dyadic j)) := by
        apply Finset.prod_congr rfl
        intro j _
        rw [show dyadic j - dyadic k = -(dyadic k - dyadic j) by ring, div_neg]
      _ = _ := by rw [Finset.prod_neg, Finset.card_range]; rfl
  have hright : (∏ j ∈ Finset.Ico (k + 1) (N + 1),
      (1 + dyadic j) / (dyadic j - dyadic k)) = tailWeight k (N - k) := by
    rw [Finset.prod_Ico_eq_prod_range]
    rw [show N + 1 - (k + 1) = N - k by omega]
    apply Finset.prod_congr rfl
    intro j _
    rw [show k + 1 + j = k + j + 1 by omega]
    rfl
  rw [hleft, hright]

def seeleyWeight (k : ℕ) : ℝ := (-1 : ℝ) ^ k * leftWeight k * tailLimit k

theorem finiteWeight_tendsto (k : ℕ) :
    Tendsto (fun N => finiteWeight N k) atTop (𝓝 (seeleyWeight k)) := by
  have ht := (tailWeight_tendsto k).comp (tendsto_sub_atTop_nat k)
  have hc : Tendsto (fun N => ((-1 : ℝ) ^ k * leftWeight k) * tailWeight k (N - k))
      atTop (𝓝 (seeleyWeight k)) := tendsto_const_nhds.mul ht
  apply hc.congr'
  filter_upwards [eventually_ge_atTop k] with N hN
  exact (finiteWeight_factor N k hN).symm

end Yau.F04Proof.Seeley

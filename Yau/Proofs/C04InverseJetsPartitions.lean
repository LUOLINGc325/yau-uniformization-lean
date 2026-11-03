import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! The single leading block in the genuine Faà di Bruno inverse-jet recurrence. -/

noncomputable section
open Finset

namespace Yau.Proofs.C04Aux

def inverseJetCoarse (n : ℕ) (hn : 0 < n) : OrderedFinpartition n where
  length := 1
  partSize _ := n
  partSize_pos _ := hn
  emb _ := id
  emb_strictMono _ := strictMono_id
  parts_strictMono := Subsingleton.strictMono _
  disjoint := by intro i hi j hj hij; exact False.elim (hij (Subsingleton.elim i j))
  cover i := ⟨0, i, rfl⟩

theorem inverseJet_partition_sum_sizes {n : ℕ} (c : OrderedFinpartition n) :
    ∑ i : Fin c.length, c.partSize i = n := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using Fintype.card_congr c.equivSigma

theorem inverseJet_coarse_of_length_one {n : ℕ} (hn : 0 < n)
    (c : OrderedFinpartition n) (hc : c.length = 1) : c = inverseJetCoarse n hn := by
  have hsum := inverseJet_partition_sum_sizes c
  rcases c with ⟨length, partSize, partSize_pos, emb, emb_strictMono,
    parts_strictMono, disjoint, cover⟩
  dsimp only at hc
  subst length
  have hsize : partSize = fun _ => n := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa only [Fin.sum_univ_one] using hsum
  subst partSize
  have hemb : emb = fun _ => id := by
    funext i j
    exact congrFun (emb_strictMono i).eq_id j
  subst emb
  rfl

theorem inverseJet_partition_part_lt {n : ℕ} (hn : 0 < n)
    (c : OrderedFinpartition n) (hc : c ≠ inverseJetCoarse n hn) (i : Fin c.length) :
    c.partSize i < n := by
  have hlen : 1 < c.length := by
    have hp := c.length_pos hn
    by_contra hh
    exact hc (inverseJet_coarse_of_length_one hn c (by omega))
  letI : Nontrivial (Fin c.length) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨j, hji⟩ := exists_ne i
  have hs : c.partSize i + c.partSize j ≤ n := by
    calc
      c.partSize i + c.partSize j = ∑ k ∈ ({i, j} : Finset (Fin c.length)), c.partSize k := by
        simp [hji, hji.symm]
      _ ≤ ∑ k : Fin c.length, c.partSize k :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = n := inverseJet_partition_sum_sizes c
  have hjpos := c.partSize_pos j
  omega

end Yau.Proofs.C04Aux

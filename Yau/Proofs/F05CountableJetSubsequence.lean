import Yau.Proofs.F05BootstrapCompactHolder

/-! Countably many compact coordinate cylinders admit one actual uniform
subsequence. This is Tychonoff plus the native Arzelà–Ascoli theorem in
the countable product of bounded-continuous function spaces. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem F05_countable_holder_compact_subsequence {n : ℕ} {ι V : Type*} [Countable ι]
    [NormedAddCommGroup V] [ProperSpace V] (Q : ι → Set (Point n))
    (hQ : ∀ i, IsCompact (Q i)) (α C : ι → ℝ) (hα : ∀ i, 0 < α i)
    (f : ℕ → ι → Point n → V) (hf : ∀ k i, HolderBound (α i) (Q i) (f k i) (C i)) :
    ∃ (φ : ℕ → ℕ) (g : ι → Point n → V), StrictMono φ ∧
      ∀ i, TendstoUniformlyOn (fun k => f (φ k) i) (g i) atTop (Q i) := by
  classical
  letI (i : ι) : CompactSpace (Q i) := isCompact_iff_compactSpace.mp (hQ i)
  let F : ℕ → ∀ i : ι, BoundedContinuousFunction (Q i) V := fun k i =>
    BoundedContinuousFunction.mkOfCompact
      ⟨fun z => f k i z.val,(holderBound_continuousOn (hα i) (hf k i)).domRestrict⟩
  let K (i : ι) := closure (range (fun k => F k i))
  have hCompact (i : ι) : IsCompact (K i) := by
    have hIn : ∀ (g : BoundedContinuousFunction (Q i) V) (z : Q i),
        g ∈ range (fun k => F k i) → g z ∈ Metric.closedBall 0 (C i) := by
      intro g z hg
      obtain ⟨k,rfl⟩ := hg
      rw [Metric.mem_closedBall,dist_zero_right]
      exact (hf k i).2.1 z.val z.property
    have hEqui : Equicontinuous (fun g : range (fun k => F k i) =>
        (g.val : Q i → V)) := by
      apply F05_holder_family_equicontinuous (hα i)
      intro g z w
      obtain ⟨k,hk⟩ := g.property
      rw [← hk]
      exact (hf k i).2.2 z.val z.property w.val w.property
    exact BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : V) (C i))
      (isCompact_closedBall 0 (C i)) (range (fun k => F k i)) hIn hEqui
  have hProduct : IsCompact {g : ∀ i : ι, BoundedContinuousFunction (Q i) V | ∀ i, g i ∈ K i} :=
    isCompact_pi_infinite hCompact
  obtain ⟨g,hg,φ,hφ,hConv⟩ := hProduct.tendsto_subseq
    (fun k i => subset_closure (mem_range_self k))
  let gFull : ι → Point n → V := fun i z => if hz : z ∈ Q i then g i ⟨z,hz⟩ else 0
  refine ⟨φ,gFull,hφ,?_⟩
  intro i
  have hUniform := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
    (tendsto_pi_nhds.mp hConv i)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hUniform ε hε] with k hk z hz
  have hkz := hk ⟨z,hz⟩
  change dist (g i ⟨z,hz⟩) (f (φ k) i z) < ε at hkz
  simpa only [gFull,dite_eq_left hz] using hkz

theorem F05_countable_eventual_holder_subsequence {n : ℕ} {ι V : Type*} [Countable ι]
    [NormedAddCommGroup V] [ProperSpace V] (Q : ι → Set (Point n))
    (hQ : ∀ i, IsCompact (Q i)) (α C : ι → ℝ) (hα : ∀ i, 0 < α i)
    (f : ℕ → ι → Point n → V)
    (hf : ∀ i, ∀ᶠ k in atTop, HolderBound (α i) (Q i) (f k i) (C i)) :
    ∃ (φ : ℕ → ℕ) (g : ι → Point n → V), StrictMono φ ∧
      ∀ i, TendstoUniformlyOn (fun k => f (φ k) i) (g i) atTop (Q i) := by
  classical
  have hThreshold : ∀ i, ∃ N : ℕ, ∀ k ≥ N, HolderBound (α i) (Q i) (f k i) (C i) :=
    fun i => eventually_atTop.mp (hf i)
  choose N hN using hThreshold
  let fSafe := fun k i => f (max k (N i)) i
  obtain ⟨φ,g,hφ,hg⟩ := F05_countable_holder_compact_subsequence Q hQ α C hα fSafe
    (fun k i => hN i (max k (N i)) (le_max_right _ _))
  refine ⟨φ,g,hφ,?_⟩
  intro i U hU
  filter_upwards [hg i U hU,hφ.tendsto_atTop.eventually (eventually_ge_atTop (N i))] with k hk hki
  intro z hz
  simpa only [fSafe,max_eq_left hki] using hk z hz

end Yau.Proofs.F05Aux

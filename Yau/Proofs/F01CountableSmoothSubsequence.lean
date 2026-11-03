import Yau.Proofs.F01IndexedUniformSubsequence
import Yau.Proofs.F01CompactSmoothSubsequence

/-! Actual derivative bounds on countably many compact convex chart
domains produce one common subsequence and smooth compatible-order limits.
No repeated independent subsequence is supplied by the caller. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BoundedContinuousFunction NNReal
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem countable_smooth_subsequence
    (S : ℕ → Set E) (hS : ∀ j, Convex ℝ (S j)) (hcompact : ∀ j, IsCompact (S j))
    (hUnique : ∀ j, UniqueDiffOn ℝ (S j))
    (f : ℕ → ℕ → E → F) (hf : ∀ m j, ContDiffOn ℝ ∞ (f m j) (S j))
    (C : ℕ → ℕ → ℝ≥0)
    (hbound : ∀ j k m x, x ∈ S j → ‖iteratedFDerivWithin ℝ k (f m j) (S j) x‖ ≤ C j k) :
    ∃ g : ℕ → E → F, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (∀ j, ContDiffOn ℝ ∞ (g j) (S j)) ∧
      ∀ j k : ℕ, TendstoUniformlyOn
        (fun m x => iteratedFDerivWithin ℝ k (f (σ m) j) (S j) x)
        (iteratedFDerivWithin ℝ k (g j) (S j)) atTop (S j) := by
  classical
  letI (j : ℕ) : CompactSpace (S j) := isCompact_iff_compactSpace.mp (hcompact j)
  let J : ℕ → Type _ := fun k => ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F
  letI (k : ℕ) : FiniteDimensional ℝ (J k) :=
    FiniteDimensional.of_injective ContinuousMultilinearMap.toMultilinearMapLinear
      ContinuousMultilinearMap.toMultilinearMap_injective
  have hTaylor (m j : ℕ) : HasFTaylorSeriesUpToOn ∞ (f m j)
      (ftaylorSeriesWithin ℝ (f m j) (S j)) (S j) :=
    (hf m j).ftaylorSeriesWithin (hUnique j)
  have hc (m j k : ℕ) : ContinuousOn (iteratedFDerivWithin ℝ k (f m j) (S j)) (S j) :=
    (hTaylor m j).cont k (by simp)
  let u : ℕ → ∀ i : ℕ × ℕ, S i.1 →ᵇ J i.2 := fun m i =>
    BoundedContinuousFunction.mkOfCompact
      ⟨(fun x : S i.1 => iteratedFDerivWithin ℝ i.2 (f m i.1) (S i.1) x), (hc m i.1 i.2).restrict⟩
  have hLip (i : ℕ × ℕ) (m : ℕ) : LipschitzWith (C i.1 (i.2 + 1)) (fun x => u m i x) := by
    have hk : (i.2 : ℕ∞ω) < ∞ := by exact_mod_cast (ENat.natCast_lt_top i.2)
    apply convex_derivative_bound_lipschitz (hS i.1) (iteratedFDerivWithin ℝ i.2 (f m i.1) (S i.1))
      (fun x => (iteratedFDerivWithin ℝ (i.2 + 1) (f m i.1) (S i.1) x).curryLeft) (C i.1 (i.2 + 1))
    · exact fun x hx => (hTaylor m i.1).fderivWithin i.2 hk x hx
    · intro x hx
      simpa only [ContinuousMultilinearMap.curryLeft_norm] using hbound i.1 (i.2 + 1) m x hx
  have hEqui (i : ℕ × ℕ) : Equicontinuous (fun m x => u m i x) :=
    (LipschitzWith.uniformEquicontinuous (fun m x => u m i x) (C i.1 (i.2 + 1)) (hLip i)).equicontinuous
  obtain ⟨v, σ, hσ, hconv⟩ := indexed_uniform_subsequence u hEqui
    (fun i => (C i.1 i.2 : ℝ)) (fun i m x => hbound i.1 i.2 m x x.property)
  let q : ℕ → E → FormalMultilinearSeries ℝ E F := fun j x k =>
    if hx : x ∈ S j then v (j, k) ⟨x, hx⟩ else 0
  have hUniformJet (j k : ℕ) : TendstoUniformlyOn
      (fun m x => iteratedFDerivWithin ℝ k (f (σ m) j) (S j) x) (fun x => q j x k) atTop (S j) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [(Metric.tendstoUniformly_iff.mp (hconv (j, k))) ε hε] with m hm
    intro x hx
    have h := hm ⟨x, hx⟩
    change dist (v (j, k) ⟨x, hx⟩) (iteratedFDerivWithin ℝ k (f (σ m) j) (S j) x) < ε at h
    simpa only [q, dif_pos hx] using h
  have hSmooth (j : ℕ) := smooth_closed_jet_limit (hS j) (hUnique j)
    (fun m => f (σ m) j) (fun m => hf (σ m) j) (q j) (hUniformJet j)
  refine ⟨(fun j x => (q j x 0).curry0), σ, hσ, (fun j => (hSmooth j).1), ?_⟩
  intro j k
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hUniformJet j k)) ε hε] with m hm
  intro x hx
  rw [← (hSmooth j).2 k x hx]
  exact hm x hx

end Yau.NodeProofs.F01Aux

import Yau.Proofs.P03ImmersionGoodDensity
import Yau.Proofs.P03PairGoodDensity
import Yau.Proofs.P03SectionArrayAtlas

open scoped Manifold Topology
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

/-- A single finite tuple satisfies both global separation and genuine chart
immersion conditions. The countable compact conditions are imposed by one
Baire choice in the actual compact-open space of holomorphic functions. -/
theorem exists_simultaneous_scalar_tuple {n : ℕ} (M : ComplexManifold n)
    (hjets : ∀ (pts : Finset M.Carrier) (k : ℕ)
      (Pj : M.Carrier → MvPolynomial (Fin n) ℂ),
      ∃ f, IsHolomorphicFn f ∧ ∀ p ∈ pts, JetAgreeFn f p (Pj p) k) :
    ∃ f : Fin (2 * n + 1) → holomorphicFunctions M,
      (∀ x y : M.Carrier, (∀ j, (f j).1 x = (f j).1 y) → x = y) ∧
      ∀ x : M.Carrier, ∃ a : M.Carrier,
        x ∈ (extChartAt (ComplexModel n) a).source ∧
        Function.Injective (tupleDerivativeCLM a f (chartPt a x)) := by
  classical
  obtain ⟨T, hT, r, hr, hsub, hcover⟩ := exists_countable_section_array_atlas M
  letI : Countable T := hT.to_subtype
  let a : T → M.Carrier := Subtype.val
  choose K hK hKsub hKcover using fun p : T × T =>
    exists_chartPair_compact_cover (a p.1) (a p.2)
  let J := T ⊕ ((T × T) × ℕ)
  let G : J → Set (Fin (2 * n + 1) → holomorphicFunctions M) :=
    Sum.elim (fun i => immersionGoodSet (a i)
      (Metric.closedBall (chartPt (a i) (a i)) (r i)) (2 * n + 1))
      (fun p => pairGoodSet (a p.1.1) (a p.1.2) (K p.1 p.2) (2 * n + 1))
  have hopen : ∀ j, IsOpen (G j) := by
    intro j
    cases j with
    | inl i => exact immersionGoodSet_isOpen (a i) _ (isCompact_closedBall _ _) (hsub i)
    | inr p => exact pairGoodSet_isOpen _ _ _ (hK p.1 p.2) (hKsub p.1 p.2)
  have hdense : ∀ j, Dense (G j) := by
    intro j
    cases j with
    | inl i => exact immersionGoodSet_dense hjets (a i) _ (isCompact_closedBall _ _) (hsub i)
    | inr p => exact pairGoodSet_dense hjets _ _ _ (hK p.1 p.2) (hKsub p.1 p.2)
  letI : BaireSpace (Fin (2 * n + 1) → holomorphicFunctions M) :=
    holomorphicTuple_baire (2 * n + 1)
  letI : Nonempty (Fin (2 * n + 1) → holomorphicFunctions M) := ⟨0⟩
  obtain ⟨f, hf⟩ := exists_mem_all_open_dense G hopen hdense
  refine ⟨f, ?_, ?_⟩
  · intro x y heq
    by_contra hxy
    obtain ⟨i, hxi, _⟩ := hcover x
    obtain ⟨j, hyj, _⟩ := hcover y
    let z := (chartPt (a i) x, chartPt (a j) y)
    have hi : chartInv (a i) (chartPt (a i) x) = x :=
      (extChartAt (ComplexModel n) (a i)).left_inv hxi
    have hj : chartInv (a j) (chartPt (a j) y) = y :=
      (extChartAt (ComplexModel n) (a j)).left_inv hyj
    have hz : z ∈ chartPairDomain (a i) (a j) := by
      refine ⟨⟨(extChartAt (ComplexModel n) (a i)).map_source hxi,
        (extChartAt (ComplexModel n) (a j)).map_source hyj⟩, ?_⟩
      change chartInv (a i) (chartPt (a i) x) ≠ chartInv (a j) (chartPt (a j) y)
      simpa only [hi, hj] using hxy
    have hzcover : z ∈ ⋃ k, K (i, j) k := by rw [hKcover]; exact hz
    obtain ⟨k, hzk⟩ := mem_iUnion.mp hzcover
    have hnonzero := hf (Sum.inr ((i, j), k)) ⟨z, hzk⟩
    apply hnonzero
    funext l
    change (f l).1 (chartInv (a i) (chartPt (a i) x)) -
      (f l).1 (chartInv (a j) (chartPt (a j) y)) = 0
    rw [hi, hj, heq l, sub_self]
  · intro x
    obtain ⟨i, hxi, hzi⟩ := hcover x
    exact ⟨a i, hxi, hf (Sum.inl i) ⟨chartPt (a i) x, Metric.ball_subset_closedBall hzi⟩⟩

end Yau.NodeProofs.P03Aux

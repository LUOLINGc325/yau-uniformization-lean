import Yau.Proofs.D04Comparison
import Yau.Proofs.D04LocalCompactness
import Yau.LeafProofs.L09

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace Yau.Proofs.D04Aux

open Yau Yau.Blueprint

variable {n : ℕ}

/-- A countable compact exhaustion promotes actual a.e. data to its open
domain; the predicate may include both infinite-value exclusions. -/
theorem ae_on_open_of_ae_on_compacts
    {O : Set (ComplexVector n)} (hO : IsOpen O) {P : ComplexVector n → Prop}
    (hP : ∀ K : Set (ComplexVector n), IsCompact K → K ⊆ O → ∀ᵐ y ∂volume.restrict K, P y) :
    ∀ᵐ y ∂volume.restrict O, P y := by
  obtain ⟨K, hK, hKO, _, hcover⟩ := exists_compact_exhaustion hO
  have hall : ∀ᵐ y ∂volume, ∀ m : ℕ, y ∈ K m → P y :=
    ae_all_iff.mpr fun m => (ae_restrict_iff' (hK m).measurableSet).mp (hP (K m) (hK m) (hKO m))
  apply (ae_restrict_iff' hO.measurableSet).mpr
  filter_upwards [hall] with y hy hyO
  obtain ⟨m, hm⟩ := hcover {y} isCompact_singleton (singleton_subset_iff.mpr hyO)
  exact hy m (hm (mem_singleton y))

theorem psh_eq_of_locally_ae_eq
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    {p q : ComplexVector n → EReal} (hp : IsPshOn p O) (hq : IsPshOn q O)
    (hae : ∀ K : Set (ComplexVector n), IsCompact K → K ⊆ O → p =ᵐ[volume.restrict K] q) :
    Set.EqOn p q O :=
  psh_eq_of_ae_eq hO hp hq (ae_on_open_of_ae_on_compacts hO hae)

/-- Candidate representatives are identified from the same sequence after
its actual integrable tail. No early real-valued input is assumed integrable. -/
theorem finite_L1_limits_unique_of_eventually_integrable
    {u : ℕ → ComplexVector n → EReal} {p q : ComplexVector n → EReal}
    {K : Set (ComplexVector n)}
    (hu : ∃ N : ℕ, ∀ j, N ≤ j → IntegrableOn (fun y => (u j y).toReal) K volume)
    (hp : (∀ᵐ y ∂volume.restrict K, p y ≠ ⊥ ∧ p y ≠ ⊤) ∧
      IntegrableOn (fun y => (p y).toReal) K volume)
    (hq : (∀ᵐ y ∂volume.restrict K, q y ≠ ⊥ ∧ q y ≠ ⊤) ∧
      IntegrableOn (fun y => (q y).toReal) K volume)
    (hpc : Tendsto (fun j => ∫ y in K, |(u j y).toReal - (p y).toReal|) atTop (𝓝 0))
    (hqc : Tendsto (fun j => ∫ y in K, |(u j y).toReal - (q y).toReal|) atTop (𝓝 0)) :
    p =ᵐ[volume.restrict K] q := by
  obtain ⟨N, hN⟩ := hu
  have hreal : (fun y => (p y).toReal) =ᵐ[volume.restrict K] (fun y => (q y).toReal) :=
    Yau.LeafProofs.L08_L1_limit_unique (fun j => hN (j + N) (by omega)) hp.2 hq.2
      (hpc.comp (tendsto_add_atTop_nat N)) (hqc.comp (tendsto_add_atTop_nat N))
  filter_upwards [hp.1, hq.1, hreal] with y hyp hyq heq
  rw [← EReal.coe_toReal hyp.2 hyp.1, ← EReal.coe_toReal hyq.2 hyq.1, heq]

/-- The compact exhaustion retains its nested open interiors for exact disc
and limit gluing, rather than dropping that part of the exhaustion data. -/
theorem exists_nested_open_compact_exhaustion
    {D : Set (ComplexVector n)} (hD : IsOpen D) :
    ∃ (O K : ℕ → Set (ComplexVector n)),
      (∀ m, IsOpen (O m) ∧ IsCompact (K m) ∧ O m ⊆ K m ∧ K m ⊆ O (m + 1) ∧ K m ⊆ D) ∧
      Monotone O ∧ ∀ S : Set (ComplexVector n), IsCompact S → S ⊆ D → ∃ m, S ⊆ O m := by
  let : LocallyCompactSpace D := hD.locallyCompactSpace
  let E := CompactExhaustion.choice D
  let K : ℕ → Set (ComplexVector n) := fun m => (Subtype.val : D → ComplexVector n) '' E m
  let O : ℕ → Set (ComplexVector n) := fun m =>
    (Subtype.val : D → ComplexVector n) '' interior (E m)
  have hEmb : Topology.IsOpenEmbedding (Subtype.val : D → ComplexVector n) :=
    hD.isOpenEmbedding_subtypeVal
  refine ⟨O, K, ?_, ?_, ?_⟩
  · intro m
    refine ⟨hEmb.isOpenMap _ isOpen_interior,
      (E.isCompact m).image continuous_subtype_val, image_mono interior_subset, ?_, ?_⟩
    · exact image_mono (E.subset_interior_succ m)
    · rintro y ⟨x, _, rfl⟩
      exact x.2
  · intro i j hij
    exact image_mono (interior_mono (E.subset hij))
  · intro S hS hSD
    have hpre : IsCompact ((Subtype.val : D → ComplexVector n) ⁻¹' S) := by
      apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
      rw [image_preimage_eq_of_subset (by simpa only [Subtype.range_coe] using hSD)]
      exact hS
    obtain ⟨m, hm⟩ := E.exists_superset_of_isCompact hpre
    refine ⟨m + 1, ?_⟩
    intro y hy
    exact ⟨⟨y, hSD hy⟩, E.subset_interior_succ m (hm hy), rfl⟩

end Yau.Proofs.D04Aux

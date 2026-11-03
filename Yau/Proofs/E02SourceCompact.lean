import Yau.Proofs.E02EnvelopeV01Test
import Yau.Proofs.E02ProductMaps
import Yau.Proofs.E02CompactNeighborhood

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- ONE source compactum and ONE genuine envelope bound are constructed
before κ, for every factor over the compact product evaluation region.
An extra harmless domain point makes nonemptiness independent of m. -/
theorem exists_original_source_compact {n m : ℕ}
    (X : KahlerManifold n) (h : Flow X) (hh : MetricFamilySmooth h (Ici 0))
    (T : ℝ) (x : Pt X) (a : ComplexVector n × ℝ)
    (ha : (a.1,(0 : ComplexVector n),a.2) ∈ envelopeDomain X T x)
    (O : Set (ProductPoint n m)) (hOC : IsCompact (closure O))
    (hDom : ∀ Q ∈ closure O, ∀ i : Fin m, (Q.1,Q.2.2 i,Q.2.1) ∈ envelopeDomain X T x) :
    ∃ (K S : Set (EuclideanSpace ℝ (Fin (4*n+1)))) (M : ℝ),
      IsCompact K ∧ K.Nonempty ∧ IsCompact S ∧ S.Nonempty ∧ S ⊆ interior K ∧ 0 < M ∧
      (∀ q ∈ K, (envelopeRealCoordinates n).symm q ∈ envelopeDomain X T x) ∧
      LowerSemicontinuousOn (packedEnvelopeReal X h T x) K ∧
      (∀ q ∈ K, 0 ≤ packedEnvelopeReal X h T x q ∧ packedEnvelopeReal X h T x q ≤ M) ∧
      (∀ Q ∈ closure O, ∀ i : Fin m, factorProjection n m i (productRealCoordinates n m Q) ∈ S) := by
  let E : Set (ComplexVector n × ComplexVector n × ℝ) :=
    insert (a.1,0,a.2) (⋃ i : Fin m, (fun Q : ProductPoint n m => (Q.1,Q.2.2 i,Q.2.1)) '' closure O)
  have hEach (i : Fin m) : IsCompact
      ((fun Q : ProductPoint n m => (Q.1,Q.2.2 i,Q.2.1)) '' closure O) :=
    hOC.image (by fun_prop)
  have hE : IsCompact E := (isCompact_iUnion hEach).insert _
  have hNE : E.Nonempty := ⟨(a.1,0,a.2),mem_insert _ _⟩
  have hEU : E ⊆ envelopeDomain X T x := by
    intro p hp
    rcases hp with rfl|hp
    · exact ha
    · obtain ⟨i,Q,hQ,rfl⟩ := mem_iUnion.mp hp
      exact hDom Q hQ i
  obtain ⟨Kₚ,hKₚ,hKNE,hEK,hKU⟩ := exists_compact_source E (envelopeDomain X T x)
    hE hNE (isOpen_envelopeDomain X T x) hEU
  let e := envelopeRealCoordinates n
  let K := e '' Kₚ
  let S := e '' E
  have hK : IsCompact K := hKₚ.image e.continuous
  have hS : IsCompact S := hE.image e.continuous
  have hSK : S ⊆ interior K := by
    rintro q ⟨p,hp,rfl⟩
    exact e.isOpenMap.image_interior_subset Kₚ ⟨p,hEK hp,rfl⟩
  have hKD : ∀ q ∈ K, e.symm q ∈ envelopeDomain X T x := by
    rintro q ⟨p,hp,rfl⟩
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hKU hp
  have hv : LowerSemicontinuousOn (packedEnvelopeReal X h T x) K :=
    (chartEnvelopeReal_lowerSemicontinuousOn X h T x).comp e.symm.continuous.continuousOn hKD
  obtain ⟨M,hM,hBound⟩ := chartEnvelopeReal_compact_bounds X h hh T x Kₚ hKₚ hKU
  refine ⟨K,S,M,hK,hKNE.image e,hS,hNE.image e,hSK,hM,hKD,hv,?_,?_⟩
  · rintro q ⟨p,hp,rfl⟩
    simpa only [packedEnvelopeReal,e,ContinuousLinearEquiv.symm_apply_apply] using hBound p hp
  · intro Q hQ i
    rw [factorProjection_on_product]
    exact mem_image_of_mem e (mem_insert_of_mem _ (mem_iUnion.mpr ⟨i,⟨Q,hQ,rfl⟩⟩))

end Yau.NodeProofs.E02Aux

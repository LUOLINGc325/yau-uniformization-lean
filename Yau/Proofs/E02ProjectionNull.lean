import Yau.Proofs.E02ProductPacking

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace Yau.NodeProofs.E02Aux

/-- Native Haar disintegration is the Fubini argument for a surjective
finite-dimensional linear projection. The scalar may be infinite; absolute
continuity and null preimages still hold, with no finiteness assertion. -/
theorem surjective_euclidean_projection_quasiMeasurePreserving {D d : ℕ}
    (L : EuclideanSpace ℝ (Fin D) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hL : Function.Surjective L) : QuasiMeasurePreserving L volume volume := by
  refine ⟨L.continuous.measurable,?_⟩
  obtain ⟨c,_hc,hMap⟩ := L.toLinearMap.exists_map_addHaar_eq_smul_addHaar volume volume hL
  change Measure.map (L.toLinearMap) volume ≪ volume
  rw [hMap]
  exact Measure.smul_absolutelyContinuous

theorem factorProjection_quasiMeasurePreserving (n m : ℕ) (i : Fin m) :
    QuasiMeasurePreserving (factorProjection n m i) volume volume :=
  surjective_euclidean_projection_quasiMeasurePreserving (factorProjection n m i)
    (factorProjection_surjective n m i)

/-- This applies to arbitrary outer-null bad sets; measurability of the
Aleksandrov exceptional set is not an extra assumption. -/
theorem factorProjection_preimage_null (n m : ℕ) (i : Fin m)
    (N : Set (EuclideanSpace ℝ (Fin (4*n+1)))) (hN : volume N = 0) :
    volume ((factorProjection n m i) ⁻¹' N) = 0 :=
  (factorProjection_quasiMeasurePreserving n m i).preimage_null hN

theorem factorProjection_bad_union_null (n m : ℕ)
    (N : Set (EuclideanSpace ℝ (Fin (4*n+1)))) (hN : volume N = 0) :
    volume (⋃ i : Fin m, (factorProjection n m i) ⁻¹' N) = 0 :=
  measure_iUnion_null (fun i => factorProjection_preimage_null n m i N hN)

/-- One product point has good second-order jets in every factor. Its
base and physical time are the single shared coordinates of that point. -/
theorem exists_simultaneous_good_projection (n m : ℕ)
    (S : Set (EuclideanSpace ℝ (Fin (2*n+1+2*n*m)))) (hS : 0 < volume S)
    (N : Set (EuclideanSpace ℝ (Fin (4*n+1)))) (hN : volume N = 0) :
    ∃ Q ∈ S, ∀ i : Fin m, factorProjection n m i Q ∉ N := by
  by_contra h
  have hSub : S ⊆ ⋃ i : Fin m, (factorProjection n m i) ⁻¹' N := by
    intro Q hQ
    by_contra hBad
    apply h
    refine ⟨Q,hQ,?_⟩
    intro i hi
    exact hBad (mem_iUnion.mpr ⟨i,hi⟩)
  have hZero : volume S = 0 := measure_mono_null hSub (factorProjection_bad_union_null n m N hN)
  exact hS.ne' hZero

end Yau.NodeProofs.E02Aux

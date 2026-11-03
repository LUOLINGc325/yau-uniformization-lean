import Yau.LeafProofs.L23LocalDistanceSupportEscape

/-! Finite vertex energy has a genuine compact minimizer in the spatial buffer. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
variable {n N : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 800000

def fieldPolygonPoint (q y : M.Carrier) (v : Fin N → M.Carrier)
    (i : Fin (N+2)) : M.Carrier :=
  Fin.cases q (Fin.lastCases y v) i

def fieldPolygonEnergy (h : HermitianField M) (q y : M.Carrier)
    (v : Fin N → M.Carrier) : ℝ :=
  (N+1 : ℕ) * ∑ i : Fin (N+1), inducedDistance h
    (fieldPolygonPoint q y v i.castSucc) (fieldPolygonPoint q y v i.succ) ^ 2

theorem continuous_fieldPolygonPoint (q y : M.Carrier) (i : Fin (N+2)) :
    Continuous (fun v : Fin N → M.Carrier => fieldPolygonPoint q y v i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_const
  · change Continuous (fun v : Fin N → M.Carrier => Fin.lastCases (motive := fun _ : Fin (N+1) => M.Carrier) y v j)
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simpa only [Fin.lastCases_last] using
        (continuous_const : Continuous (fun _ : Fin N → M.Carrier => y))
    · simpa only [Fin.lastCases_castSucc] using
        (continuous_apply k : Continuous (fun v : Fin N → M.Carrier => v k))

theorem continuous_fieldPolygonEnergy (h : HermitianField M) (hh : MetricSmooth h)
    (q y : M.Carrier) : Continuous (fieldPolygonEnergy (N := N) h q y) := by
  apply continuous_const.mul
  apply continuous_finset_sum
  intro i _
  exact ((continuous_inducedDistance h hh).comp
    ((continuous_fieldPolygonPoint q y i.castSucc).prodMk
      (continuous_fieldPolygonPoint q y i.succ))).pow 2

theorem exists_minimizing_fieldPolygonEnergy
    (h : HermitianField M) (hh : MetricSmooth h) (S : Set M.Carrier)
    (hS : IsCompact S) (q y : M.Carrier) (hq : q ∈ S) (N : ℕ) :
    ∃ v : Fin N → M.Carrier, (∀ i, v i ∈ S) ∧
      ∀ w : Fin N → M.Carrier, (∀ i, w i ∈ S) →
        fieldPolygonEnergy h q y v ≤ fieldPolygonEnergy h q y w := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  letI : Nonempty S := ⟨⟨q,hq⟩⟩
  let e : (Fin N → S) → ℝ := fun v => fieldPolygonEnergy h q y (fun i => (v i).val)
  have hval : Continuous (fun v : Fin N → S => (fun i : Fin N => (v i).val)) :=
    continuous_pi (fun i => (continuous_apply i).subtype_val)
  have hc : Continuous e := (continuous_fieldPolygonEnergy (N := N) h hh q y).comp hval
  have hcompact : IsCompact (Set.univ : Set (Fin N → S)) := isCompact_univ
  obtain ⟨v,_,hmin⟩ := hcompact.exists_isMinOn
    (Set.univ_nonempty : (Set.univ : Set (Fin N → S)).Nonempty) hc.continuousOn
  refine ⟨fun i => (v i).val, fun i => (v i).property, ?_⟩
  intro w hw
  exact hmin (a := fun i => (⟨w i,hw i⟩ : S)) (Set.mem_univ _)

end Yau.LeafProofs.L23Aux

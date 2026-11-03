import Yau.Proofs.HeatSmoothExhaustionBoundary
import Yau.Proofs.HeatSmoothExhaustionConnectedHull

noncomputable section
open Set Filter
open scoped Topology

namespace Yau.Proofs.SmoothExhaustionAux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem exists_smoothPrecompactDomain_superset {K : Set M.Carrier} (hK : IsCompact K) :
    ∃ O : Set M.Carrier, HeatConcreteBindings.SmoothPrecompactDomain O ∧ K ⊆ O := by
  obtain ⟨L,hLc,hLconn,hKL⟩ := exists_compact_connected_superset hK
  obtain ⟨f,hf,hneg,hcompact,hreg⟩ := regular_function_around_compact hLc
  obtain ⟨o,ho⟩ := hLconn.nonempty
  let O := connectedComponentIn {p | f p < 0} o
  refine ⟨O,component_negative_smoothPrecompact hf hcompact hreg (hneg o ho),?_⟩
  exact hKL.trans (hLconn.isPreconnected.subset_connectedComponentIn ho (fun p hp => hneg p hp))

theorem smoothExhaustion_exists (M : ComplexManifold n) :
    ∃ O : ℕ → Set M.Carrier, HeatConcreteBindings.SmoothExhaustion O := by
  classical
  letI : LocallyCompactSpace M.Carrier := ChartedSpace.locallyCompactSpace (ComplexVector n) M.Carrier
  let C := CompactExhaustion.choice M.Carrier
  let Domain := {O : Set M.Carrier // HeatConcreteBindings.SmoothPrecompactDomain O}
  let chooseDomain : {K : Set M.Carrier // IsCompact K} → Domain := fun K =>
    ⟨(exists_smoothPrecompactDomain_superset K.property).choose,
      (exists_smoothPrecompactDomain_superset K.property).choose_spec.1⟩
  have hchoose (K : {K : Set M.Carrier // IsCompact K}) : K.val ⊆ (chooseDomain K).val :=
    (exists_smoothPrecompactDomain_superset K.property).choose_spec.2
  let E : ℕ → Domain := Nat.rec (chooseDomain ⟨C 0,C.isCompact 0⟩)
    (fun j D => chooseDomain ⟨C (j+1) ∪ closure D.val,
      (C.isCompact (j+1)).union D.property.2.2.2.1⟩)
  have hcover (j : ℕ) : C j ⊆ (E j).val := by
    cases j with
    | zero => exact hchoose ⟨C 0,C.isCompact 0⟩
    | succ j =>
        exact (subset_union_left : C (j+1) ⊆ C (j+1) ∪ closure (E j).val).trans
          (hchoose ⟨C (j+1) ∪ closure (E j).val,
            (C.isCompact (j+1)).union (E j).property.2.2.2.1⟩)
  refine ⟨fun j => (E j).val,fun j => (E j).property,?_,?_⟩
  · intro j
    exact (subset_union_right : closure (E j).val ⊆ C (j+1) ∪ closure (E j).val).trans
      (hchoose ⟨C (j+1) ∪ closure (E j).val,
        (C.isCompact (j+1)).union (E j).property.2.2.2.1⟩)
  · apply iUnion_eq_univ_iff.mpr
    intro p
    obtain ⟨j,hj⟩ := C.exists_mem p
    exact ⟨j,hcover j hj⟩

theorem smoothExhaustionExistenceTarget : ∀ (n : ℕ) (X : KahlerManifold n),
    HeatConcreteBindings.SmoothExhaustionExistenceTarget X := by
  intro n X
  exact smoothExhaustion_exists X.manifold

end Yau.Proofs.SmoothExhaustionAux

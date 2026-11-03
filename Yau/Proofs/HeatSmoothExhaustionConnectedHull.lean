import Yau.Proofs.HeatSmoothExhaustionCharts

noncomputable section
open Set Filter
open scoped Topology

namespace Yau.Proofs.SmoothExhaustionAux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem exists_compact_connected_superset {K : Set M.Carrier} (hK : IsCompact K) :
    ∃ L : Set M.Carrier, IsCompact L ∧ IsConnected L ∧ K ⊆ L := by
  letI : LocallyCompactSpace M.Carrier := ChartedSpace.locallyCompactSpace (ComplexVector n) M.Carrier
  letI : LocallyConnectedSpace M.Carrier := ChartedSpace.locallyConnectedSpace (ComplexVector n) M.Carrier
  let o : M.Carrier := Classical.arbitrary _
  let C := CompactExhaustion.choice M.Carrier
  let U : ℕ → Set M.Carrier := fun j => interior (C j)
  let D : ℕ → Set M.Carrier := fun j => connectedComponentIn (U j) o
  have hUmono : Monotone U := fun i j hij => interior_mono (C.subset hij)
  have hDmono : Monotone D := fun i j hij => connectedComponentIn_mono o (hUmono hij)
  have hDo (j : ℕ) : IsOpen (D j) := isOpen_interior.connectedComponentIn
  have hUcover (x : M.Carrier) : ∃ j, x ∈ U j := by
    obtain ⟨j,hj⟩ := C.exists_mem x
    exact ⟨j+1,C.subset_interior_succ j hj⟩
  have hDnon : (⋃ j, D j).Nonempty := by
    obtain ⟨j,hj⟩ := hUcover o
    exact ⟨o,mem_iUnion_of_mem j (mem_connectedComponentIn hj)⟩
  have hCompl : IsOpen (⋃ j, D j)ᶜ := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨j,hj⟩ := hUcover x
    let W := connectedComponentIn (U j) x
    have hWo : IsOpen W := isOpen_interior.connectedComponentIn
    have hxW : x ∈ W := mem_connectedComponentIn hj
    apply mem_of_superset (hWo.mem_nhds hxW)
    intro y hy hyD
    obtain ⟨k,hk⟩ := mem_iUnion.mp hyD
    let m := max j k
    have hyW : y ∈ connectedComponentIn (U m) x :=
      connectedComponentIn_mono x (hUmono (le_max_left j k)) hy
    have hyDm : y ∈ D m := hDmono (le_max_right j k) hk
    have heq : connectedComponentIn (U m) x = D m :=
      (connectedComponentIn_eq hyW).trans (connectedComponentIn_eq hyDm).symm
    have hxDm : x ∈ D m := heq ▸ mem_connectedComponentIn (hUmono (le_max_left j k) hj)
    exact hx (mem_iUnion_of_mem m hxDm)
  have hDall : (⋃ j, D j) = univ :=
    (IsClopen.eq_univ ⟨isOpen_compl_iff.mp hCompl,isOpen_iUnion hDo⟩ hDnon)
  obtain ⟨j,hj⟩ := (hK.union isCompact_singleton).elim_directed_cover D hDo
    (by rw [hDall];exact subset_univ _) hDmono.directed_le
  have hoD : o ∈ D j := hj (Or.inr (mem_singleton o))
  have hDj : IsConnected (D j) := isConnected_connectedComponentIn_iff.mpr
    (connectedComponentIn_subset (U j) o hoD)
  have hclosure : closure (D j) ⊆ C j := closure_minimal
    ((connectedComponentIn_subset (U j) o).trans interior_subset) (C.isCompact j).isClosed
  refine ⟨closure (D j),(C.isCompact j).of_isClosed_subset isClosed_closure hclosure,
    hDj.closure,?_⟩
  intro x hx
  exact subset_closure (hj (Or.inl hx))

end Yau.Proofs.SmoothExhaustionAux

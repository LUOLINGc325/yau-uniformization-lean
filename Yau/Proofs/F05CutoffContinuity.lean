import Mathlib

/-! A coefficient supported inside a genuine coordinate neighborhood extends
continuous physical data by zero across the artificial coordinate edge. -/

open Set Filter
open scoped Topology
noncomputable section

namespace Yau.Proofs.F05Aux

theorem F05_continuousOn_cutoff_operation {Z E F G : Type*}
    [TopologicalSpace Z] [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]
    [Zero E] [Zero G] {U Q : Set Z} (hU : IsOpen U)
    (B : E → F → G) (hB : Continuous (fun p : E × F => B p.1 p.2))
    (hZero : ∀ y, B 0 y = 0) {a : Z → E} {f : Z → F}
    (ha : Continuous a) (hf : ContinuousOn f (U ∩ Q)) (hSupport : tsupport a ⊆ U) :
    ContinuousOn (fun x => B (a x) (f x)) Q := by
  intro x hx
  by_cases hs : x ∈ tsupport a
  · have hUN : U ∈ 𝓝[Q] x := nhdsWithin_le_nhds (hU.mem_nhds (hSupport hs))
    have hfN : ContinuousWithinAt f Q x :=
      (hf x ⟨hSupport hs,hx⟩).mono_of_mem_nhdsWithin (inter_mem hUN self_mem_nhdsWithin)
    exact hB.continuousAt.comp_continuousWithinAt (ha.continuousAt.continuousWithinAt.prodMk hfN)
  · have hz : a =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hs
    have hEq : (fun z => B (a z) (f z)) =ᶠ[𝓝 x] 0 := by
      filter_upwards [hz] with z hz
      rw [hz,Pi.zero_apply,hZero,Pi.zero_apply]
    exact (continuousAt_const.congr_of_eventuallyEq hEq).continuousWithinAt

end Yau.Proofs.F05Aux

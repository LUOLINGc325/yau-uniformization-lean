import Yau.Proofs.P04CanonicalNormContinuous

noncomputable section
open Set
open scoped Topology Manifold

namespace Yau.Proofs.P04Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

/-- Lindelof selection preserves every already proved property of the
constructed sections and yields a sequence nonvanishing at every point. -/
theorem countable_nonvanishing_sections (g : SmoothMetric M)
    (P : CanonicalSection M → Prop)
    (hex : ∀ x : M.Carrier, ∃ S : CanonicalSection M,
      P S ∧ IsHolomorphicCanonical S ∧ S x ≠ 0) :
    ∃ S : ℕ → CanonicalSection M,
      (∀ i, P (S i) ∧ IsHolomorphicCanonical (S i)) ∧
      ∀ x : M.Carrier, ∃ i, S i x ≠ 0 := by
  classical
  choose S hP hS hne using hex
  let V : M.Carrier → Set M.Carrier := fun a => {x | 0 < canonicalNormSq g.form (S a) x}
  have hV (a : M.Carrier) : IsOpen (V a) :=
    isOpen_Ioi.preimage (canonicalNormSq_continuous g (S a) (hS a))
  have hself (a : M.Carrier) : a ∈ V a := by
    apply lt_of_le_of_ne' (canonicalNormSq_nonneg g.form (S a) a)
    intro hz
    exact hne a ((canonicalNormSq_eq_zero_iff g.form (S a) a).mp hz)
  have hcover : (⋃ a, V a)=univ := by
    apply eq_univ_of_forall
    intro x
    exact mem_iUnion.mpr ⟨x,hself x⟩
  obtain ⟨T,hT,hTU⟩ := TopologicalSpace.isOpen_iUnion_countable V hV
  have hcoverT : (⋃ a ∈ T, V a)=univ := hTU.trans hcover
  have hTne : T.Nonempty := by
    let a : M.Carrier := Classical.choice inferInstance
    have ha : a ∈ ⋃ b ∈ T, V b := by rw [hcoverT]; trivial
    obtain ⟨b,hb⟩ := mem_iUnion.mp ha
    obtain ⟨hbT,_⟩ := mem_iUnion.mp hb
    exact ⟨b,hbT⟩
  obtain ⟨t,ht⟩ := hT.exists_eq_range hTne
  refine ⟨fun i => S (t i),fun i => ⟨hP _,hS _⟩,fun x => ?_⟩
  have hx : x ∈ ⋃ a ∈ T, V a := by rw [hcoverT]; trivial
  obtain ⟨a,ha⟩ := mem_iUnion.mp hx
  obtain ⟨haT,haV⟩ := mem_iUnion.mp ha
  rw [ht] at haT
  obtain ⟨i,rfl⟩ := haT
  refine ⟨i,?_⟩
  intro hz
  have hzero := (canonicalNormSq_eq_zero_iff g.form (S (t i)) x).mpr hz
  exact (ne_of_gt haV) hzero

end Yau.Proofs.P04Aux

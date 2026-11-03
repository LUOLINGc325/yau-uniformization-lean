import Yau.Proofs.F04EnergySeparability

open Filter TopologicalSpace Set
open scoped Topology

noncomputable section

namespace Yau.F04Proof

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [SeparableSpace V]

/-- These are finite spans in the given energy space itself. -/
def variationalGalerkinSequence : ℕ → V := denseSeq V

theorem variationalGalerkinSequence_denseRange : DenseRange (variationalGalerkinSequence V) :=
  denseRange_denseSeq V

def variationalGalerkinSpace (m : ℕ) : Submodule ℝ V :=
  Submodule.span ℝ (Set.range (fun k : Fin m => variationalGalerkinSequence V k))

instance variationalGalerkinSpace_finiteDimensional (m : ℕ) :
    FiniteDimensional ℝ (variationalGalerkinSpace V m) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

@[simp] theorem variationalGalerkinSpace_zero : variationalGalerkinSpace V 0 = ⊥ := by
  simp [variationalGalerkinSpace]

theorem variationalGalerkinSequence_mem {k m : ℕ} (hkm : k < m) :
    variationalGalerkinSequence V k ∈ variationalGalerkinSpace V m :=
  Submodule.subset_span ⟨⟨k, hkm⟩, rfl⟩

theorem variationalGalerkinSpace_monotone : Monotone (variationalGalerkinSpace V) := by
  intro m l hml
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  exact variationalGalerkinSequence_mem V (lt_of_lt_of_le k.isLt hml)

theorem variationalGalerkinSpace_eventually_mem {m : ℕ} {v : V}
    (hv : v ∈ variationalGalerkinSpace V m) :
    ∀ᶠ l in atTop, v ∈ variationalGalerkinSpace V l := by
  filter_upwards [eventually_ge_atTop m] with l hl
  exact variationalGalerkinSpace_monotone V hl hv

theorem variationalGalerkinSpace_dense_union :
    Dense (⋃ m, (variationalGalerkinSpace V m : Set V)) := by
  apply (variationalGalerkinSequence_denseRange V).mono
  rintro _ ⟨k, rfl⟩
  exact Set.mem_iUnion.mpr ⟨k + 1, variationalGalerkinSequence_mem V (Nat.lt_succ_self k)⟩

end Yau.F04Proof

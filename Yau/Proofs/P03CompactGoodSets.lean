import Yau.Geometry.Basic
import Mathlib.Topology.Maps.Proper.Basic

open scoped Topology
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

/-- A jointly continuous open condition imposed at every point of a
compact parameter set is open in the function parameter. -/
theorem isOpen_compact_forall {A K Y : Type*}
    [TopologicalSpace A] [TopologicalSpace K] [CompactSpace K] [TopologicalSpace Y]
    (g : A × K → Y) (hg : Continuous g) {R : Set Y} (hR : IsOpen R) :
    IsOpen {a : A | ∀ k : K, g (a, k) ∈ R} := by
  have hc : IsClosed (Prod.fst '' (g ⁻¹' Rᶜ)) :=
    isClosedMap_fst_of_compactSpace _ (hR.isClosed_compl.preimage hg)
  have heq : {a : A | ∀ k : K, g (a, k) ∈ R} = (Prod.fst '' (g ⁻¹' Rᶜ))ᶜ := by
    ext a
    constructor
    · intro h ⟨⟨a', k⟩, hk, ha⟩
      change a' = a at ha
      subst a'
      exact hk (h k)
    · intro h k
      by_contra hk
      exact h ⟨(a, k), hk, rfl⟩
  rw [heq]
  exact hc.isOpen_compl

theorem isOpen_compact_injective {A K E F : Type*}
    [TopologicalSpace A] [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (g : A × K → E →L[ℂ] F) (hg : Continuous g) :
    IsOpen {a : A | ∀ k : K, Function.Injective (g (a, k))} :=
  isOpen_compact_forall g hg ContinuousLinearMap.isOpen_injective

theorem isOpen_compact_nonzero {A K F : Type*}
    [TopologicalSpace A] [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace F] [T1Space F] [Zero F]
    (g : A × K → F) (hg : Continuous g) :
    IsOpen {a : A | ∀ k : K, g (a, k) ≠ 0} :=
  isOpen_compact_forall g hg isClosed_singleton.isOpen_compl

/-- Density in a finite-dimensional perturbation family implies closure
at every point of that family in the original function space. -/
theorem mem_closure_of_dense_parameters {A P : Type*}
    [TopologicalSpace A] [TopologicalSpace P] (f : P → A) (hf : Continuous f)
    {G : Set A} (hd : Dense (f ⁻¹' G)) (p : P) : f p ∈ closure G :=
  (show MapsTo f (f ⁻¹' G) G from fun _ h => h).closure hf (hd p)

/-- One Baire choice satisfies the entire countable family, in its original
nonempty parameter space. -/
theorem exists_mem_all_open_dense {A J : Type*} [TopologicalSpace A]
    [BaireSpace A] [Nonempty A] [Countable J] (G : J → Set A)
    (ho : ∀ j, IsOpen (G j)) (hd : ∀ j, Dense (G j)) :
    ∃ a, ∀ j, a ∈ G j := by
  obtain ⟨a, ha⟩ := (dense_iInter_of_isOpen ho hd).nonempty
  exact ⟨a, mem_iInter.mp ha⟩

end Yau.NodeProofs.P03Aux

import spec.CHAIN.CONTRACTS

/-! Uncompiled F01 scratch: genuine connected sublevel components, their
compact cofinality, and the actual open-submanifold structure. No regular
value or nonvanishing-gradient condition is used. -/
open Set TopologicalSpace
open scoped Topology Manifold
noncomputable section
namespace Yau.NodeProofs.F01Aux

variable {A : Type*} [TopologicalSpace A]

def sublevelComponent (u : A → ℝ) (o : A) (L : ℝ) : Set A :=
  connectedComponentIn (u ⁻¹' Iio L) o

theorem sublevelComponent_mono (u : A → ℝ) (o : A) :
    Monotone (sublevelComponent u o) := by
  intro L D hLD
  exact connectedComponentIn_mono o (fun x hx => lt_of_lt_of_le hx hLD)

theorem sublevelComponent_subset (u : A → ℝ) (o : A) (L : ℝ) :
    sublevelComponent u o L ⊆ u ⁻¹' Iio L :=
  connectedComponentIn_subset _ _

theorem sublevelComponent_isOpen [LocallyConnectedSpace A]
    {u : A → ℝ} (hu : Continuous u) (o : A) (L : ℝ) :
    IsOpen (sublevelComponent u o L) :=
  (isOpen_Iio.preimage hu).connectedComponentIn

theorem sublevelComponent_isConnected {u : A → ℝ} {o : A} {L : ℝ}
    (ho : u o < L) : IsConnected (sublevelComponent u o L) :=
  isConnected_connectedComponentIn_iff.mpr ho

theorem exists_mem_sublevelComponent [PathConnectedSpace A]
    {u : A → ℝ} (hu : Continuous u) (o x : A) :
    ∃ L : ℝ, x ∈ sublevelComponent u o L := by
  let γ := PathConnectedSpace.somePath o x
  have hc : IsCompact (range γ) := isCompact_range γ.continuous
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn hu.continuousOn
  have hrange : range γ ⊆ u ⁻¹' Iio (B + 1) := by
    intro y hy
    have h := hB y hy
    have hyB : u y ≤ B := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using h)
    exact lt_of_le_of_lt hyB (lt_add_one B)
  have hoγ : o ∈ range γ := ⟨0, by simp [γ]⟩
  have hxγ : x ∈ range γ := ⟨1, by simp [γ]⟩
  exact ⟨B + 1, ((isConnected_range γ.continuous).isPreconnected.subset_connectedComponentIn
    hoγ hrange) hxγ⟩

theorem compact_subset_sublevelComponent [PathConnectedSpace A] [LocallyConnectedSpace A]
    {u : A → ℝ} (hu : Continuous u) (o : A) {K : Set A} (hK : IsCompact K) :
    ∃ L : ℝ, ∀ D ≥ L, K ⊆ sublevelComponent u o D := by
  have hcover : K ⊆ ⋃ L : ℝ, sublevelComponent u o L := by
    intro x _
    obtain ⟨L, hL⟩ := exists_mem_sublevelComponent hu o x
    exact mem_iUnion.mpr ⟨L, hL⟩
  obtain ⟨L, hL⟩ := hK.elim_directed_cover (sublevelComponent u o)
    (fun D => sublevelComponent_isOpen hu o D) hcover
    (fun D E => ⟨max D E, sublevelComponent_mono u o (le_max_left _ _),
      sublevelComponent_mono u o (le_max_right _ _)⟩)
  exact ⟨L, fun D hD => hL.trans (sublevelComponent_mono u o hD)⟩

theorem noncompact_nonempty_open [T2Space A] [PreconnectedSpace A] [NoncompactSpace A]
    {S : Set A} (hS : IsOpen S) (hne : S.Nonempty) : ¬IsCompact S := by
  intro hc
  have he : S = univ := (show IsClopen S from ⟨hc.isClosed, hS⟩).eq_univ hne
  exact NoncompactSpace.noncompact_univ (he ▸ hc)

/-- Actual restriction of the original complex manifold to an open connected
nonempty set. All tangent maps used later are derivatives of its inclusion. -/
def openConnectedManifold {n : ℕ} (M : Yau.ComplexManifold n)
    (S : Opens M.Carrier) (hS : IsConnected (S : Set M.Carrier)) :
    Yau.ComplexManifold n := by
  letI : ConnectedSpace S := isConnected_iff_connectedSpace.mp hS
  letI : NoncompactSpace S := ⟨by
    intro hcompact
    have hSc : IsCompact (S : Set M.Carrier) :=
      isCompact_iff_compactSpace.mpr (isCompact_univ_iff.mp hcompact)
    exact noncompact_nonempty_open S.isOpen hS.nonempty hSc⟩
  exact {
    Carrier := S
    topology := inferInstance
    charted := inferInstance
    manifold := inferInstance
    t2 := inferInstance
    secondCountable := inferInstance
    connected := inferInstance
    noncompact := inferInstance
    dimension := n
    dimension_eq := rfl }

end Yau.NodeProofs.F01Aux

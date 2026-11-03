import Yau.Proofs.D04Distance

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace Yau.Proofs.D04Aux

open Yau.Blueprint

theorem lintegral_finset_biUnion_le {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset ι) (A : ι → Set X) (f : X → ENNReal) :
    (∫⁻ x in ⋃ i ∈ s, A i, f x ∂μ) ≤ ∑ i ∈ s, ∫⁻ x in A i, f x ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.set_biUnion_insert, Finset.sum_insert hi]
      exact (lintegral_union_le f (A i) (⋃ k ∈ s, A k)).trans (add_le_add le_rfl ih)

/-- Exact agreement of local representatives on a countable paired cover
assembles their actual compact integrals, original EReal errors, and Hartogs
bounds. No global measurability of early input potentials is assumed. -/
theorem assemble_manifold_psh_limits
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (V C W : ℕ → Set X)
    (hVopen : ∀ i, IsOpen (V i)) (hCcompact : ∀ i, IsCompact (C i))
    (hVC : ∀ i, V i ⊆ C i) (hCW : ∀ i, C i ⊆ W i) (hWopen : ∀ i, IsOpen (W i))
    (hVcover : (⋃ i, V i) = univ)
    (p : ℕ → X → EReal) (hpUSC : ∀ i, UpperSemicontinuous (p i))
    (hpTop : ∀ i x, x ∈ W i → p i x < ⊤)
    (heq : ∀ i j, EqOn (p i) (p j) (W i ∩ W j))
    (hfinite : ∀ i, ∀ᵐ x ∂μ.restrict (C i), p i x ≠ ⊥)
    (us : ℕ → X → EReal) (φ : ℕ → ℕ)
    (hlocal : ∀ i K, IsCompact K → K ⊆ W i →
      IntegrableOn (fun x => (p i x).toReal) K μ ∧
        Tendsto (fun j => ∫⁻ x in K, erealDist (us (φ j) x) (p i x) ∂μ) atTop (𝓝 0))
    (hhartogs : ∀ (i : ℕ) (c : ℝ), (∀ x ∈ W i, p i x = (c : EReal)) →
      ∀ K, IsCompact K → K ⊆ W i → ∀ ε : ℝ, 0 < ε →
        ∃ N, ∀ j, N ≤ j → ∀ x ∈ K, us (φ j) x ≤ ((c + ε : ℝ) : EReal)) :
    ∃ u : X → EReal,
      UpperSemicontinuous u ∧ (∀ x, u x < ⊤) ∧ (∀ᵐ x ∂μ, u x ≠ ⊥) ∧
      (∀ i, EqOn u (p i) (W i)) ∧
      (∀ K, IsCompact K → IntegrableOn (fun x => (u x).toReal) K μ ∧
        Tendsto (fun j => ∫⁻ x in K, erealDist (us (φ j) x) (u x) ∂μ) atTop (𝓝 0)) ∧
      (∀ c : ℝ, (∀ x, u x = (c : EReal)) → ∀ K, IsCompact K → ∀ ε : ℝ, 0 < ε →
        ∃ N, ∀ j, N ≤ j → ∀ x ∈ K, us (φ j) x ≤ ((c + ε : ℝ) : EReal)) := by
  classical
  have hmem (x : X) : ∃ i, x ∈ W i := by
    have hx : x ∈ ⋃ i, V i := by rw [hVcover]; exact mem_univ x
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact ⟨i, hCW i (hVC i hi)⟩
  let idx : X → ℕ := fun x => Classical.choose (hmem x)
  let u : X → EReal := fun x => p (idx x) x
  have hueq (i : ℕ) : EqOn u (p i) (W i) := by
    intro x hx
    exact heq (idx x) i ⟨Classical.choose_spec (hmem x), hx⟩
  have huUSC : UpperSemicontinuous u := by
    intro x a ha
    let i : ℕ := idx x
    have hxi : x ∈ W i := Classical.choose_spec (hmem x)
    have hpa : p i x < a := by simpa only [u, i] using ha
    filter_upwards [hpUSC i x a hpa, (hWopen i).mem_nhds hxi] with y hy hyW
    rw [hueq i hyW]
    exact hy
  have huTop (x : X) : u x < ⊤ := hpTop (idx x) x (Classical.choose_spec (hmem x))
  have huFinite : ∀ᵐ x ∂μ, u x ≠ ⊥ := by
    have hCi (i : ℕ) : ∀ᵐ x ∂μ, x ∈ C i → u x ≠ ⊥ := by
      apply (ae_restrict_iff' (hCcompact i).measurableSet).mp
      filter_upwards [hfinite i, ae_restrict_mem (hCcompact i).measurableSet] with x hx hxC
      rw [hueq i (hCW i hxC)]
      exact hx
    filter_upwards [ae_all_iff.mpr hCi] with x hx
    have hxV : x ∈ ⋃ i, V i := by rw [hVcover]; exact mem_univ x
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxV
    exact hx i (hVC i hi)
  have hcoverCompact (K : Set X) (hK : IsCompact K) :
      ∃ s : Finset ℕ, K ⊆ ⋃ i ∈ s, V i :=
    hK.elim_finite_subcover V hVopen (by rw [hVcover]; exact subset_univ K)
  refine ⟨u, huUSC, huTop, huFinite, hueq, ?_, ?_⟩
  · intro K hK
    obtain ⟨s, hs⟩ := hcoverCompact K hK
    let A : ℕ → Set X := fun i => K ∩ C i
    have hAc (i : ℕ) : IsCompact (A i) := hK.inter (hCcompact i)
    have hAW (i : ℕ) : A i ⊆ W i := fun _ hx => hCW i hx.2
    have hKA : K ⊆ ⋃ i ∈ s, A i := by
      intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hs hx)
      obtain ⟨his, hix⟩ := mem_iUnion.mp hi
      exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨his, hx, hVC i hix⟩⟩
    have hAi (i : ℕ) : IntegrableOn (fun x => (u x).toReal) (A i) μ := by
      apply ((hlocal i (A i) (hAc i) (hAW i)).1).congr
      filter_upwards [ae_restrict_mem (hAc i).measurableSet] with x hx
      rw [hueq i (hAW i hx)]
    have hiUnion : IntegrableOn (fun x => (u x).toReal) (⋃ i ∈ s, A i) μ :=
      integrableOn_finset_iUnion.mpr (fun i _ => hAi i)
    refine ⟨hiUnion.mono_set hKA, ?_⟩
    have hEi (i : ℕ) : Tendsto
        (fun j => ∫⁻ x in A i, erealDist (us (φ j) x) (u x) ∂μ) atTop (𝓝 0) := by
      apply ((hlocal i (A i) (hAc i) (hAW i)).2).congr'
      apply Filter.Eventually.of_forall
      intro j
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (hAc i).measurableSet] with x hx
      rw [hueq i (hAW i hx)]
    have hsum : Tendsto
        (fun j => ∑ i ∈ s, ∫⁻ x in A i, erealDist (us (φ j) x) (u x) ∂μ) atTop (𝓝 0) := by
      simpa only [Finset.sum_const_zero] using tendsto_finsetSum s (fun i _ => hEi i)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun _ : ℕ => (0 : ENNReal)) tendsto_const_nhds hsum (fun _ => bot_le)
    intro j
    exact (lintegral_mono_set hKA).trans
      (lintegral_finset_biUnion_le μ s A (fun x => erealDist (us (φ j) x) (u x)))
  · intro c hc K hK ε hε
    obtain ⟨s, hs⟩ := hcoverCompact K hK
    let A : ℕ → Set X := fun i => K ∩ C i
    have hAi (i : ℕ) : ∀ᶠ j in atTop, ∀ x ∈ A i, us (φ j) x ≤ ((c + ε : ℝ) : EReal) := by
      apply eventually_atTop.mpr
      exact hhartogs i c (fun x hx => (hueq i hx).symm.trans (hc x))
        (A i) (hK.inter (hCcompact i)) (fun _ hx => hCW i hx.2) ε hε
    have hall : ∀ᶠ j in atTop, ∀ i ∈ s, ∀ x ∈ A i, us (φ j) x ≤ ((c + ε : ℝ) : EReal) :=
      (eventually_all_finset s).mpr (fun i _ => hAi i)
    apply eventually_atTop.mp
    filter_upwards [hall] with j hj
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hs hx)
    obtain ⟨his, hix⟩ := mem_iUnion.mp hi
    exact hj i his x ⟨hx, hVC i hix⟩

end Yau.Proofs.D04Aux

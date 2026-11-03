import Yau.Blueprint.Nodes

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace Yau.Proofs.D04Aux

open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

/-- The frozen carrier assumptions themselves rule out complex dimension zero. -/
theorem dimension_pos (M : ComplexManifold n) : 0 < n := by
  by_contra hn
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  let : DiscreteTopology M.Carrier :=
    ChartedSpace.discreteTopology (ComplexVector 0) M.Carrier
  let : Subsingleton M.Carrier := PreconnectedSpace.trivial_of_discrete
  let : CompactSpace M.Carrier := inferInstance
  exact (isCompact_univ : IsCompact (Set.univ : Set M.Carrier)).ne_univ rfl

/-- A moving point in a fixed compact set excludes uniform collapse there.
This part of the lower-anchor argument needs no analytic hypotheses. -/
theorem not_collapse_of_point_anchor
    {us : ℕ → M.Carrier → EReal} {phi : ℕ → ℕ}
    {K : Set M.Carrier} {z : ℕ → M.Carrier} {A : ℝ}
    (hK : IsCompact K)
    (hz : ∀ j, z j ∈ K ∧ ((-A : ℝ) : EReal) ≤ us (phi j) (z j)) :
    ¬ ManifoldPshCollapse us phi := by
  intro hcollapse
  obtain ⟨J, hJ⟩ := hcollapse K hK (A + 1)
  have h := (hz J).2.trans (hJ J le_rfl (z J) (hz J).1)
  have hreal : -A ≤ -(A + 1) := EReal.coe_le_coe_iff.mp h
  linarith

/-- Positive measure supplies a point anchor even when the anchored sets move.
Neither measurability nor a choice of all the points is needed. -/
theorem not_collapse_of_positive_measure_anchor
    (μ : Measure M.Carrier) {us : ℕ → M.Carrier → EReal} {phi : ℕ → ℕ}
    {K : Set M.Carrier} {Es : ℕ → Set M.Carrier} {A c : ℝ}
    (hK : IsCompact K) (hc : 0 < c)
    (hEs : ∀ j, Es j ⊆ K ∧ ENNReal.ofReal c ≤ μ (Es j) ∧
      ∀ x ∈ Es j, ((-A : ℝ) : EReal) ≤ us (phi j) x) :
    ¬ ManifoldPshCollapse us phi := by
  intro hcollapse
  obtain ⟨J, hJ⟩ := hcollapse K hK (A + 1)
  have hnonempty : (Es J).Nonempty := by
    by_contra hempty
    have hzero : μ (Es J) = 0 := by rw [Set.not_nonempty_iff_eq_empty.mp hempty]; simp
    have hpos : 0 < ENNReal.ofReal c := ENNReal.ofReal_pos.mpr hc
    exact (not_le_of_gt hpos) (hzero ▸ (hEs J).2.1)
  obtain ⟨x, hx⟩ := hnonempty
  have h := ((hEs J).2.2 x hx).trans (hJ J le_rfl x ((hEs J).1 hx))
  have hreal : -A ≤ -(A + 1) := EReal.coe_le_coe_iff.mp h
  linarith

/-- Every fixed compact lies in all sufficiently late exhausting domains. -/
theorem compact_eventually_subset_exhaustion
    {Ωs : ℕ → Set M.Carrier}
    (hΩ : ∀ j, IsOpen (Ωs j) ∧ Ωs j ⊆ Ωs (j + 1))
    (hcover : (⋃ j, Ωs j) = Set.univ) {K : Set M.Carrier} (hK : IsCompact K) :
    ∃ J, ∀ j, J ≤ j → K ⊆ Ωs j := by
  have hmono : Monotone Ωs := monotone_nat_of_le_succ (fun j => (hΩ j).2)
  obtain ⟨J, hJ⟩ := hK.elim_directed_cover Ωs (fun j => (hΩ j).1)
    (by rw [hcover]; exact Set.subset_univ K)
    (fun i j => ⟨max i j, hmono (le_max_left _ _), hmono (le_max_right _ _)⟩)
  exact ⟨J, fun j hj => hJ.trans (hmono hj)⟩

/-- The same tail property holds after any strictly increasing extraction. -/
theorem compact_eventually_subset_subsequence
    {Ωs : ℕ → Set M.Carrier}
    (hΩ : ∀ j, IsOpen (Ωs j) ∧ Ωs j ⊆ Ωs (j + 1))
    (hcover : (⋃ j, Ωs j) = Set.univ) {K : Set M.Carrier} (hK : IsCompact K)
    {phi : ℕ → ℕ} (hphi : StrictMono phi) :
    ∃ J, ∀ j, J ≤ j → K ⊆ Ωs (phi j) := by
  obtain ⟨J, hJ⟩ := compact_eventually_subset_exhaustion hΩ hcover hK
  exact ⟨J, fun j hj => hJ (phi j) (hj.trans (hphi.id_le j))⟩

/-- Uniform collapse persists through a further subsequence. -/
theorem collapse_subsequence
    {us : ℕ → M.Carrier → EReal} {phi σ : ℕ → ℕ}
    (hcollapse : ManifoldPshCollapse us phi) (hσ : StrictMono σ) :
    ManifoldPshCollapse us (phi ∘ σ) := by
  intro K hK A
  obtain ⟨J, hJ⟩ := hcollapse K hK A
  exact ⟨J, fun j hj => hJ (σ j) (hj.trans (hσ.id_le j))⟩

/-- Failure of uniform collapse supplies an actual lower-anchored subsequence.
The points remain in the same fixed compact and in the original domains. -/
theorem collapse_or_point_anchored_subsequence
    {Ωs : ℕ → Set M.Carrier} {us : ℕ → M.Carrier → EReal}
    (hΩ : ∀ j, IsOpen (Ωs j) ∧ Ωs j ⊆ Ωs (j + 1))
    (hcover : (⋃ j, Ωs j) = Set.univ) :
    ManifoldPshCollapse us id ∨
      ∃ (phi : ℕ → ℕ) (K : Set M.Carrier) (z : ℕ → M.Carrier) (A : ℝ),
        StrictMono phi ∧ IsCompact K ∧
          ∀ j, z j ∈ K ∧ z j ∈ Ωs (phi j) ∧
            ((-A : ℝ) : EReal) ≤ us (phi j) (z j) := by
  classical
  by_cases hcollapse : ManifoldPshCollapse us id
  · exact Or.inl hcollapse
  · right
    simp only [ManifoldPshCollapse, id_eq] at hcollapse
    push Not at hcollapse
    obtain ⟨K, hK, A, hbad⟩ := hcollapse
    obtain ⟨N, hN⟩ := compact_eventually_subset_exhaustion hΩ hcover hK
    have hf : ∃ᶠ j in atTop, ∃ x, x ∈ K ∧ x ∈ Ωs j ∧
        ((-A : ℝ) : EReal) ≤ us j x := by
      rw [frequently_atTop]
      intro J
      obtain ⟨j, hj, x, hx, hxbound⟩ := hbad (max J N)
      refine ⟨j, (le_max_left J N).trans hj, x, hx, ?_, hxbound.le⟩
      exact hN j ((le_max_right J N).trans hj) hx
    obtain ⟨phi, hphi, hpoints⟩ := extraction_of_frequently_atTop hf
    choose z hz using hpoints
    exact ⟨phi, K, z, A, hphi, hK, hz⟩

/-- The upper-bound hypothesis in D04 becomes a genuine bound on each compact
tail, including after extraction. -/
theorem eventually_uniform_upper_bound
    {Ωs : ℕ → Set M.Carrier} {us : ℕ → M.Carrier → EReal}
    (hΩ : ∀ j, IsOpen (Ωs j) ∧ Ωs j ⊆ Ωs (j + 1))
    (hcover : (⋃ j, Ωs j) = Set.univ)
    (hbound : ∀ K : Set M.Carrier, IsCompact K → ∃ C : ℝ, ∀ j,
      K ⊆ Ωs j → ∀ x ∈ K, us j x ≤ (C : EReal))
    {K : Set M.Carrier} (hK : IsCompact K) {phi : ℕ → ℕ} (hphi : StrictMono phi) :
    ∃ (C : ℝ) (J : ℕ), ∀ j, J ≤ j → ∀ x ∈ K, us (phi j) x ≤ (C : EReal) := by
  obtain ⟨C, hC⟩ := hbound K hK
  obtain ⟨J, hJ⟩ := compact_eventually_subset_subsequence hΩ hcover hK hphi
  exact ⟨C, J, fun j hj => hC (phi j) (hJ j hj)⟩

/-- Chartwise psh functions restrict to smaller open domains. -/
theorem isPshOn_mono {m : ℕ} {u : ComplexVector m → EReal}
    {U V : Set (ComplexVector m)} (hu : IsPshOn u V) (hUV : U ⊆ V) :
    IsPshOn u U := by
  refine ⟨fun z hz => hu.1 z (hUV hz), hu.2.1.mono hUV, ?_⟩
  intro z w hdisc φ hφ hmajor
  exact hu.2.2 z w (fun ζ hζ => hUV (hdisc ζ hζ)) φ hφ hmajor

/-- Restriction retains the same function and induced charts. -/
theorem pshOnManifold_mono {u : M.Carrier → EReal} {U V : Set M.Carrier}
    (hu : PshOnManifold u V) (hUV : U ⊆ V) : PshOnManifold u U := by
  refine ⟨fun x hx => hu.1 x (hUV hx), hu.2.1.mono hUV, ?_⟩
  intro x
  exact isPshOn_mono (hu.2.2 x) (fun _ hz => ⟨hz.1, hUV hz.2⟩)

/-- On the whole manifold the open-domain predicate gives exactly the original
global psh predicate, with no replacement of the representative. -/
theorem isPsh_of_pshOnManifold_univ {u : M.Carrier → EReal}
    (hu : PshOnManifold u Set.univ) : IsPsh u := by
  refine ⟨fun x => hu.1 x (Set.mem_univ x),
    upperSemicontinuousOn_univ_iff.mp hu.2.1, ?_⟩
  intro x z w hdisc φ hφ hmajor
  exact (hu.2.2 x).2.2 z w (fun ζ hζ => ⟨hdisc ζ hζ, Set.mem_univ _⟩)
    φ hφ hmajor

theorem pshOnManifold_univ_of_isPsh {u : M.Carrier → EReal}
    (hu : IsPsh u) : PshOnManifold u Set.univ := by
  refine ⟨fun x _ => hu.1 x, upperSemicontinuousOn_univ_iff.mpr hu.2.1, ?_⟩
  intro x
  refine ⟨fun z _ => hu.1 _, ?_, ?_⟩
  · exact (upperSemicontinuousOn_univ_iff.mpr hu.2.1).comp
      ((continuousOn_extChartAt_symm (I := ComplexModel n) x).mono
        (fun _ hz => hz.1)) (fun _ _ => Set.mem_univ _)
  · intro z w hdisc φ hφ hmajor
    exact hu.2.2 x z w (fun ζ hζ => (hdisc ζ hζ).1) φ hφ hmajor

theorem pshOnManifold_univ_iff {u : M.Carrier → EReal} :
    PshOnManifold u Set.univ ↔ IsPsh u :=
  ⟨isPsh_of_pshOnManifold_univ, pshOnManifold_univ_of_isPsh⟩

end Yau.Proofs.D04Aux

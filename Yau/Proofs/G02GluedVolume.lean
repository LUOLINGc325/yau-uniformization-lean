import Yau.Proofs.G02ChartOverlap

noncomputable section
open MeasureTheory
open scoped Topology Manifold ENNReal Matrix

namespace Yau.Proofs.G02Aux
open Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem exists_chart_sequence (M : ComplexManifold n) :
    ∃ c : ℕ → M.Carrier, (⋃ k, chartSource (c k)) = Set.univ := by
  obtain ⟨S, hS, hcover⟩ := isLindelof_univ.elim_countable_subcover
    (fun a : M.Carrier => chartSource a)
    (fun a => isOpen_extChartAt_source (I := ComplexModel n) a)
    (by
      simp only [chartSource, extChartAt_source, iUnion_source_chartAt]
      exact Set.Subset.rfl)
  have hSne : S.Nonempty := by
    obtain ⟨p⟩ := (inferInstance : Nonempty M.Carrier)
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ p))
    obtain ⟨haS, _⟩ := Set.mem_iUnion.mp ha
    exact ⟨a, haS⟩
  obtain ⟨c, hc⟩ := hS.exists_eq_range hSne
  refine ⟨c, Set.eq_univ_of_forall ?_⟩
  intro p
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ p))
  obtain ⟨haS, hp⟩ := Set.mem_iUnion.mp ha
  rw [hc] at haS
  obtain ⟨k, rfl⟩ := haS
  exact Set.mem_iUnion.mpr ⟨k, hp⟩

def chartPiece (c : ℕ → M.Carrier) (k : ℕ) : Set M.Carrier :=
  disjointed (fun j => chartSource (c j)) k

def gluedVolume (h : HermitianField M) (c : ℕ → M.Carrier) : Measure M.Carrier :=
  Measure.sum (fun k => (localVolume h (c k)).restrict (chartPiece c k))

theorem measurableSet_chartPiece (c : ℕ → M.Carrier) (k : ℕ) :
    MeasurableSet (chartPiece c k) :=
  MeasurableSet.disjointed (fun j => measurableSet_chartSource (c j)) k

theorem chartPiece_subset (c : ℕ → M.Carrier) (k : ℕ) :
    chartPiece c k ⊆ chartSource (c k) :=
  disjointed_subset _ k

theorem chartPiece_disjoint (c : ℕ → M.Carrier) :
    Pairwise (fun i j => Disjoint (chartPiece c i) (chartPiece c j)) :=
  disjoint_disjointed _

theorem chartPiece_cover (c : ℕ → M.Carrier)
    (hc : (⋃ k, chartSource (c k)) = Set.univ) :
    (⋃ k, chartPiece c k) = Set.univ := by
  change (⋃ k, disjointed (fun j => chartSource (c j)) k) = Set.univ
  rw [iUnion_disjointed, hc]

theorem gluedVolume_restrict_source (h : HermitianField M)
    (c : ℕ → M.Carrier) (hc : (⋃ k, chartSource (c k)) = Set.univ)
    (a : M.Carrier) :
    (gluedVolume h c).restrict (chartSource a) = localVolume h a := by
  have hUa := measurableSet_chartSource a
  have hterms : ∀ k,
      ((localVolume h (c k)).restrict (chartPiece c k)).restrict (chartSource a) =
        ((localVolume h a).restrict (chartPiece c k)).restrict (chartSource a) := by
    intro k
    apply Measure.ext
    intro t ht
    simp only [Measure.restrict_apply ht, Measure.restrict_apply (ht.inter hUa)]
    apply localVolume_eq_on_overlap h (c k) a
      ((t ∩ chartSource a) ∩ chartPiece c k)
      ((ht.inter hUa).inter (measurableSet_chartPiece c k))
    · intro p hp
      exact chartPiece_subset c k hp.2
    · intro p hp
      exact hp.1.2
  have hsum : Measure.sum (fun k =>
      (localVolume h a).restrict (chartPiece c k)) = localVolume h a := by
    rw [← Measure.restrict_iUnion (chartPiece_disjoint c)
      (measurableSet_chartPiece c), chartPiece_cover c hc, Measure.restrict_univ]
  calc
    (gluedVolume h c).restrict (chartSource a) =
        Measure.sum (fun k =>
          ((localVolume h (c k)).restrict (chartPiece c k)).restrict (chartSource a)) :=
      Measure.restrict_sum _ hUa
    _ = Measure.sum (fun k =>
          ((localVolume h a).restrict (chartPiece c k)).restrict (chartSource a)) :=
      congrArg Measure.sum (funext hterms)
    _ = (Measure.sum (fun k =>
          (localVolume h a).restrict (chartPiece c k))).restrict (chartSource a) :=
      (Measure.restrict_sum _ hUa).symm
    _ = (localVolume h a).restrict (chartSource a) := by rw [hsum]
    _ = localVolume h a := localVolume_restrict_source h a

theorem exists_riemannianVolume (h : HermitianField M)
    (_hsmooth : MetricSmooth h) :
    ∃ μ : Measure M.Carrier, IsRiemannianVolume h μ := by
  obtain ⟨c, hc⟩ := exists_chart_sequence M
  refine ⟨gluedVolume h c, ?_⟩
  intro a s hs hsa
  have hsa' : s ⊆ chartSource a := by
    simpa only [chartSource, extChartAt_source] using hsa
  have he := congrArg (fun ν : Measure M.Carrier => ν s)
    (gluedVolume_restrict_source h c hc a)
  rw [Measure.restrict_eq_self (gluedVolume h c) hsa'] at he
  exact he.trans (localVolume_apply_of_subset h a s hs hsa')

end Yau.Proofs.G02Aux

import Yau.Proofs.P03CompactOpenAmbient
import Yau.Geometry.Calculus

open scoped Manifold Topology
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

theorem exists_compact_cover_of_open {E : Type*} [TopologicalSpace E]
    [LocallyCompactSpace E] [SecondCountableTopology E] {U : Set E} (hU : IsOpen U) :
    ∃ K : ℕ → Set E, (∀ k, IsCompact (K k)) ∧ (∀ k, K k ⊆ U) ∧ ⋃ k, K k = U := by
  letI : LocallyCompactSpace U := hU.locallyCompactSpace
  have hs : IsSigmaCompact U := isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  obtain ⟨K, hK, hcover⟩ := hs
  refine ⟨K, hK, ?_, hcover⟩
  intro k x hx
  rw [← hcover]
  exact mem_iUnion.mpr ⟨k, hx⟩

variable {n : ℕ} {M : ComplexManifold n}

def chartPairMap (a b : M.Carrier) (z : ComplexVector n × ComplexVector n) :
    M.Carrier × M.Carrier := (chartInv a z.1, chartInv b z.2)

def chartPairDomain (a b : M.Carrier) : Set (ComplexVector n × ComplexVector n) :=
  (chartTarget a ×ˢ chartTarget b) ∩ {z | chartInv a z.1 ≠ chartInv b z.2}

theorem chartPairMap_continuousOn (a b : M.Carrier) :
    ContinuousOn (chartPairMap a b) (chartTarget a ×ˢ chartTarget b) := by
  have ha : ContinuousOn (fun z : ComplexVector n × ComplexVector n => chartInv a z.1)
      (chartTarget a ×ˢ chartTarget b) :=
    (continuousOn_extChartAt_symm (I := ComplexModel n) a).comp continuousOn_fst
      (fun z hz => hz.1)
  have hb : ContinuousOn (fun z : ComplexVector n × ComplexVector n => chartInv b z.2)
      (chartTarget a ×ˢ chartTarget b) :=
    (continuousOn_extChartAt_symm (I := ComplexModel n) b).comp continuousOn_snd
      (fun z hz => hz.2)
  exact ha.prodMk hb

theorem chartPairDomain_isOpen (a b : M.Carrier) : IsOpen (chartPairDomain a b) := by
  have ho : IsOpen {p : M.Carrier × M.Carrier | p.1 ≠ p.2} :=
    (isClosed_eq continuous_fst continuous_snd).isOpen_compl
  exact (chartPairMap_continuousOn a b).isOpen_inter_preimage
    ((isOpen_extChartAt_target a).prod (isOpen_extChartAt_target b)) ho

theorem exists_chartPair_compact_cover (a b : M.Carrier) :
    ∃ K : ℕ → Set (ComplexVector n × ComplexVector n),
      (∀ k, IsCompact (K k)) ∧ (∀ k, K k ⊆ chartPairDomain a b) ∧
      ⋃ k, K k = chartPairDomain a b :=
  exists_compact_cover_of_open (chartPairDomain_isOpen a b)

end Yau.NodeProofs.P03Aux

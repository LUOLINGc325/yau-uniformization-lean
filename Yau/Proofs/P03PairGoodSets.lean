import Yau.Proofs.P03PairCompactCover
import Yau.Proofs.P03HolomorphicEvaluation
import Yau.Proofs.P03CompactGoodSets

open scoped Manifold Topology
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n N : ℕ} {M : ComplexManifold n}

def pairGoodSet (a b : M.Carrier) (K : Set (ComplexVector n × ComplexVector n)) (N : ℕ) :
    Set (Fin N → holomorphicFunctions M) :=
  {f | ∀ z : K, (fun j => (f j).1 (chartInv a z.1.1) - (f j).1 (chartInv b z.1.2)) ≠ 0}

theorem pairGoodSet_isOpen (a b : M.Carrier) (K : Set (ComplexVector n × ComplexVector n))
    (hK : IsCompact K) (hsub : K ⊆ chartPairDomain a b) : IsOpen (pairGoodSet a b K N) := by
  letI := manifold_locallyCompact M
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hx : Continuous (fun z : K => chartInv a z.1.1) :=
    (continuousOn_extChartAt_symm (I := ComplexModel n) a).comp_continuous
      (continuous_fst.comp continuous_subtype_val) (fun z => (hsub z.2).1.1)
  have hy : Continuous (fun z : K => chartInv b z.1.2) :=
    (continuousOn_extChartAt_symm (I := ComplexModel n) b).comp_continuous
      (continuous_snd.comp continuous_subtype_val) (fun z => (hsub z.2).1.2)
  have hv (j : Fin N) : Continuous
      (fun p : (Fin N → holomorphicFunctions M) × K =>
        (p.1 j).1 (chartInv a p.2.1.1) - (p.1 j).1 (chartInv b p.2.1.2)) := by
    have hf : Continuous (fun p : (Fin N → holomorphicFunctions M) × K => (p.1 j).1) :=
      continuous_subtype_val.comp ((continuous_apply j).comp continuous_fst)
    exact (continuous_eval.comp (hf.prodMk (hx.comp continuous_snd))).sub
      (continuous_eval.comp (hf.prodMk (hy.comp continuous_snd)))
  exact isOpen_compact_nonzero _ (continuous_pi hv)

theorem holomorphicPairDifference_differentiableOn (f : holomorphicFunctions M)
    (a b : M.Carrier) :
    DifferentiableOn ℂ (fun z : ComplexVector n × ComplexVector n =>
      f.1 (chartInv a z.1) - f.1 (chartInv b z.2)) (chartTarget a ×ˢ chartTarget b) := by
  have ha : DifferentiableOn ℂ (fun z : ComplexVector n × ComplexVector n => f.1 (chartInv a z.1))
      (chartTarget a ×ˢ chartTarget b) :=
    ((mdifferentiable_iff_chartDifferentiable (f.1 : M.Carrier → ℂ)).mp f.2 a).comp
      differentiableOn_fst (fun z hz => hz.1)
  have hb : DifferentiableOn ℂ (fun z : ComplexVector n × ComplexVector n => f.1 (chartInv b z.2))
      (chartTarget a ×ˢ chartTarget b) :=
    ((mdifferentiable_iff_chartDifferentiable (f.1 : M.Carrier → ℂ)).mp f.2 b).comp
      differentiableOn_snd (fun z hz => hz.2)
  exact ha.sub hb

end Yau.NodeProofs.P03Aux

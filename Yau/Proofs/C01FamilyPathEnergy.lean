import Yau.Proofs.C01FamilyPathEnergyDensity
import Yau.Proofs.C01ParameterIntegral

/-! Integrating the actual joint path-energy density gives genuine
C2 dependence on the variation parameter and metric time. -/

noncomputable section
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint Yau.LeafProofs.L12Aux

variable {n : ℕ} {M : ComplexManifold n}

def familyActualPathEnergy {E : Type*} (h : ℝ → HermitianField M)
    (F : E → ℝ → M.Carrier) (p : E × ℝ) : ℝ := actualPathEnergy (h p.2) (F p.1)

theorem familyActualPathEnergy_contDiffOn_two
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (h : ℝ → HermitianField M) (I : Set ℝ) (hI : IsOpen I) (hh : MetricFamilySmooth h I)
    (F : E → ℝ → M.Carrier) (U : Set E) (J : Set ℝ) (hU : IsOpen U) (hJ : IsOpen J)
    (hunit : Set.Icc (0 : ℝ) 1 ⊆ J) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, E × ℝ) 𝓘(ℝ, ComplexVector n) 3 (Function.uncurry F) (U ×ˢ J) →
    ContDiffOn ℝ 2 (familyActualPathEnergy h F) (U ×ˢ I) := by
  letI := manifold_realSmooth M
  intro hF
  have HD : ContDiffOn ℝ 2 (familyActualPathEnergyDensity h F) ((U ×ˢ I) ×ˢ J) :=
    familyActualPathEnergyDensity_contDiffOn_two h I hI hh F U J hU hJ hF
  exact Parametric.contDiffOn_unitIntegral (hU.prod hI) hJ hunit 2 HD

theorem fixedActualPathEnergy_time_contDiffOn_two
    (h : ℝ → HermitianField M) (I : Set ℝ) (hI : IsOpen I) (hh : MetricFamilySmooth h I)
    (f : ℝ → M.Carrier) (J : Set ℝ) (hJ : IsOpen J) (hunit : Set.Icc (0 : ℝ) 1 ⊆ J) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 f J →
    ContDiffOn ℝ 2 (fun t => actualPathEnergy (h t) f) I := by
  letI := manifold_realSmooth M
  intro hf
  let F : ℝ → ℝ → M.Carrier := fun _ u => f u
  have hsnd : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) 3
      (Prod.snd : ℝ × ℝ → ℝ) ((Set.univ : Set ℝ) ×ˢ J) :=
    (contDiffOn_snd : ContDiffOn ℝ 3 (Prod.snd : ℝ × ℝ → ℝ) _).contMDiffOn
  have hF : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry F) ((Set.univ : Set ℝ) ×ˢ J) :=
    hf.comp hsnd (fun p hp => hp.2)
  have H := familyActualPathEnergy_contDiffOn_two h I hI hh F Set.univ J isOpen_univ hJ hunit hF
  have hγ : ContDiffOn ℝ 2 (fun t : ℝ => ((0 : ℝ), t)) I :=
    contDiffOn_const.prodMk contDiffOn_id
  have HC := H.comp hγ (fun t ht => ⟨Set.mem_univ _, ht⟩)
  exact HC

end Yau.NodeProofs.C01Aux

import Yau.Proofs.C01FixedPathEnergyDensity
import Yau.Proofs.C01ScalarParameterIntegral

/-! For a genuine fixed path the actual time derivative of its energy
is minus the integral of the actual real Ricci quadratic. -/

noncomputable section
open MeasureTheory
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint Yau.LeafProofs.L12Aux

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_actualPathEnergy_hasDerivAt
    (hflow : LocalizedFlow X o h U P ρ) (f : ℝ → Pt X)
    (J : Set ℝ) (hJ : IsOpen J) (hunit : Set.Icc (0 : ℝ) 1 ⊆ J) :
    letI := manifold_realSmooth X.manifold
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 f J → ∀ a : ℝ, 0 < a →
    HasDerivAt (fun t => actualPathEnergy (h t) f)
      (-(∫ u in Set.Icc (0 : ℝ) 1,
        actualRealRicciQuadratic (h a) (f u) (realCurveVelocity f u))) a := by
  letI := manifold_realSmooth X.manifold
  intro hf a ha
  have hh : MetricFamilySmooth h (Set.Ioi 0) := by
    intro x i j
    exact (hflow.1.2.1 x i j).mono (fun p hp => ⟨hp.1, Set.Ioi_subset_Ici_self hp.2⟩)
  have HD : ContDiffOn ℝ 2 (fixedActualPathEnergyDensity h f) (Set.Ioi 0 ×ˢ J) :=
    fixedActualPathEnergyDensity_contDiffOn_two h (Set.Ioi 0) J isOpen_Ioi hJ hh f hf
  have H := scalar_unitIntegral_hasDerivAt (fixedActualPathEnergyDensity h f)
    (Set.Ioi 0) J isOpen_Ioi hJ hunit (HD.of_le (by norm_num)) a ha
    (fun u => -actualRealRicciQuadratic (h a) (f u) (realCurveVelocity f u))
    (fun u _ => localizedFlow_fixed_energyDensity_hasDerivAt hflow f u a ha)
  rw [integral_neg] at H
  exact H

end Yau.NodeProofs.C01Aux

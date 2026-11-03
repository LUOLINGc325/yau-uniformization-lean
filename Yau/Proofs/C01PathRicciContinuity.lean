import Yau.Proofs.C01FixedPathEnergyDensity
import Yau.Proofs.C01ParameterIntegral

/-! The true Ricci quadratic along an actual C3 path is continuous,
as the genuine time derivative of its joint energy density. -/

noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.C01Aux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux
variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_pathRicci_continuousOn
    (hflow : LocalizedFlow X o h U P ρ) (γ : ℝ → Pt X)
    (J : Set ℝ) (hJ : IsOpen J) (a : ℝ) (ha : 0 < a) :
    letI := manifold_realSmooth X.manifold
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 γ J →
    ContinuousOn (fun u => actualRealRicciQuadratic (h a) (γ u) (realCurveVelocity γ u)) J := by
  letI := manifold_realSmooth X.manifold
  intro hγ
  have hh : MetricFamilySmooth h (Set.Ioi 0) := by
    intro c i j
    exact (hflow.1.2.1 c i j).mono (fun p hp => ⟨hp.1, Set.Ioi_subset_Ici_self hp.2⟩)
  let F := fixedActualPathEnergyDensity h γ
  have hF : ContDiffOn ℝ 2 F (Set.Ioi 0 ×ˢ J) :=
    fixedActualPathEnergyDensity_contDiffOn_two h (Set.Ioi 0) J isOpen_Ioi hJ hh γ hγ
  let G : ℝ × ℝ → ℝ := fun p => Parametric.parameterDerivative F p 1
  have hG : ContDiffOn ℝ 1 G (Set.Ioi 0 ×ˢ J) :=
    (Parametric.parameterDerivative_contDiffOn isOpen_Ioi hJ 1 hF).clm_apply contDiffOn_const
  have harg : ContinuousOn (fun u : ℝ => (a, u)) J :=
    continuousOn_const.prodMk continuousOn_id
  have hcont : ContinuousOn (fun u => -G (a, u)) J :=
    (hG.continuousOn.comp harg
      (fun u hu => ⟨ha, hu⟩)).neg
  apply hcont.congr
  intro u hu
  have HD : DifferentiableAt ℝ F (a, u) :=
    (hF.contDiffAt (((isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).prod hJ).mem_nhds
      (show (a, u) ∈ Set.Ioi (0 : ℝ) ×ˢ J from ⟨ha, hu⟩))).differentiableAt (by norm_num)
  have HG := (Parametric.parameterDerivative_hasFDerivAt F HD).hasDerivAt
  have HR := localizedFlow_fixed_energyDensity_hasDerivAt hflow γ u a ha
  have he : G (a, u) = -actualRealRicciQuadratic (h a) (γ u) (realCurveVelocity γ u) :=
    HG.unique HR
  simp only [he, neg_neg]

end Yau.NodeProofs.C01Aux

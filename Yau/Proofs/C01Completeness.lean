import Yau.Proofs.C01BoundaryMinimizingPath
import Yau.Proofs.C01WeightedIndexIntegral
import Yau.Proofs.C01RicciGermCongruence
import Yau.Proofs.C01PathSupportIndexEstimate
import Yau.Proofs.C01ExitCompletenessAssembly

/-! The actual first-exit profile satisfies its square-root-time barrier. Its diverging original-radius bound implies completeness of the exact positive-time length distance. -/

noncomputable section
open MeasureTheory
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.C01Aux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux
open Yau.LeafProofs.L23LocalDistanceContract
variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_complete_distance
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (T : ℝ) (hT : 0 < T) : IsCompleteDistance (lengthDist (h T)) := by
  letI := manifold_realSmooth X.manifold
  obtain ⟨Dcost, hDcost, hcost⟩ := indexCutoff_derivative_energy_bound
  let B : ℝ := (2*n : ℕ) * Dcost
  have hB : 0 ≤ B := mul_nonneg (Nat.cast_nonneg _) hDcost.le
  obtain ⟨C, hC, hsupport⟩ := localizedFlow_pathSupport_index_estimate hflow hjoint T B hT.le hB
  apply localizedFlow_complete_of_exit_support hflow T C hT.le hC
  intro L hL a ha
  obtain ⟨δ, γ, β, hδ, hγ0, hγ1, hmin, hGeo, hspeedγ, hβ, hβ0, hβ1, hnear, hspeedβ⟩ :=
    localizedFlow_exists_boundary_minimizing_path hflow a L ha.1.le hL
  have hk := localizedFlow_metricSmooth_nonneg hflow a ha.1.le
  have hunit : Set.Icc (0 : ℝ) 1 ⊆ Set.Ioo (-δ) (1+δ) := by
    intro u hu
    constructor <;> linarith [hu.1, hu.2]
  have hγAt (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ u :=
    ((hGeo.1 u (hunit hu)).contMDiffAt (isOpen_Ioo.mem_nhds (hunit hu))).of_le (by norm_num)
  have hRγ : ContinuousOn
      (fun u => actualRealRicciQuadratic (h a) (γ u) (realCurveVelocity γ u))
      (Set.Icc (0 : ℝ) 1) :=
    (localizedFlow_pathRicci_continuousOn hflow γ (Set.Ioo (-δ) (1+δ)) isOpen_Ioo a ha.1 hGeo.1).mono hunit
  have hminspeed (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      realTangentSpeedSq (h a) (γ u) (realCurveVelocity γ u) =
        inducedDistance (h a) (γ 0) (γ 1) ^ 2 := by
    simpa only [hγ0, hmin] using hspeedγ u hu
  have hindex (κ : ℝ) (hκ : 0 < κ) (hκhalf : κ ≤ 1/2) :
      (∫ u in Set.Icc (0 : ℝ) 1, indexCutoff κ u ^ 2 *
        actualRealRicciQuadratic (h a) (β u) (realCurveVelocity β u)) ≤ B / κ := by
    have hcostκ := hcost κ hκ hκhalf
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc] at hcostκ
    have H := minimizing_field_geodesic_weighted_index (h a) hk γ δ hδ hGeo hminspeed hRγ
      κ Dcost hκ hcostκ
    have HE := localizedFlow_pathRicci_weighted_integral_germ_congr hflow γ β
      (fun u => indexCutoff κ u ^ 2) hnear a ha.1 hγAt
      (fun u _ => (hβ u).of_le (by norm_num))
    rw [HE] at H
    exact H
  obtain ⟨f, D, hfa, hupper, hderiv, hbound⟩ :=
    hsupport a L ha.1 ha.2 hL β hβ hβ0 hβ1 hspeedβ hindex
  exact ⟨f, D, hfa, fun t ht => hupper t ht.1, hderiv, hbound⟩

end Yau.NodeProofs.C01Aux

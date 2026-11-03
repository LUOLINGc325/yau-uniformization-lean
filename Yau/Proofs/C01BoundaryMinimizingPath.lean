import Yau.LeafProofs.L23LocalDistanceSupportMinimizingGeodesic
import Yau.Proofs.C01BoundaryNearMinimizers
import Yau.Proofs.C01PathEnergyCongruence

/-! Compact confinement of actual near-minimizers supplies a genuine boundary minimizing geodesic. Smooth saturation preserves its path germs and actual constant speed without completeness of the positive-time metric. -/

noncomputable section
open Filter
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.C01Aux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
open Yau.LeafProofs.L23LocalDistanceContract
variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_exists_boundary_minimizing_path
    (hflow : LocalizedFlow X o h U P ρ) (a L : ℝ) (ha : 0 ≤ a) (hL : 0 < L) :
    letI := manifold_realSmooth X.manifold
    ∃ (δ : ℝ) (γ β : ℝ → Pt X), 0 < δ ∧ γ 0 = o ∧
      γ 1 ∈ initialDistanceSphere X.metric o L ∧
      inducedDistance (h a) o (γ 1) = exitDistanceProfile X.metric (h a) o L ∧
      FieldGeodesicOn (h a) γ (Set.Ioo (-δ) (1+δ)) ∧
      (∀ u ∈ Set.Icc (0 : ℝ) 1,
        realTangentSpeedSq (h a) (γ u) (realCurveVelocity γ u) =
          exitDistanceProfile X.metric (h a) o L ^ 2) ∧
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 β ∧ β 0 = o ∧
      β 1 ∈ initialDistanceSphere X.metric o L ∧
      (∀ u ∈ Set.Icc (0 : ℝ) 1, γ =ᶠ[𝓝 u] β) ∧
      (∀ u ∈ Set.Icc (0 : ℝ) 1,
        realTangentSpeedSq (h a) (β u) (realCurveVelocity β u) =
          exitDistanceProfile X.metric (h a) o L ^ 2) := by
  letI := manifold_realSmooth X.manifold
  have hk := localizedFlow_metricSmooth_nonneg hflow a ha
  obtain ⟨y, hy, hmin, _⟩ := exitDistanceProfile_attained X.metric (h a) hk o L hL.le
  have hnear := localizedFlow_boundary_confined_nearMinimizingCurves hflow a ha L hL y hy hmin.symm
  obtain ⟨δ, hδ, γ, hγ0, hγ1, hGeo, _hmap, hspeed⟩ := compactMinimizingGeodesic n X.manifold
    (h a) hk Set.univ {x | inducedDistance X.metric.form o x ≤ L+1} isOpen_univ
    (isCompact_inducedDistance_sublevel X.metric o (L+1)) (Set.subset_univ _) o y hnear
  have hunit : Set.Icc (0 : ℝ) 1 ⊆ Set.Ioo (-δ) (1+δ) := by
    intro u hu
    constructor <;> linarith [hu.1, hu.2]
  have hspeedγ (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      realTangentSpeedSq (h a) (γ u) (realCurveVelocity γ u) =
        exitDistanceProfile X.metric (h a) o L ^ 2 := by
    change actualSpeedSq (h a) γ u = _
    rw [← hmin] at hspeed
    exact hspeed u hu
  obtain ⟨χ, hχ, hχmap, hχeq⟩ := exists_smooth_unit_saturation hδ
  let β := fun u => γ (χ u)
  have hβ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 β :=
    contMDiffOn_univ.mp (hGeo.1.comp ((hχ.of_le (by simp)).contMDiff.contMDiffOn) hχmap)
  have hnearβ (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) : γ =ᶠ[𝓝 u] β := by
    filter_upwards [hχeq u hu] with s hs
    change γ s = γ (χ s)
    rw [hs]
    rfl
  have hβ0 : β 0 = o := (hnearβ 0 (by norm_num)).self_of_nhds.symm.trans hγ0
  have hβ1 : β 1 = y := (hnearβ 1 (by norm_num)).self_of_nhds.symm.trans hγ1
  have hspeedβ (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      realTangentSpeedSq (h a) (β u) (realCurveVelocity β u) =
        exitDistanceProfile X.metric (h a) o L ^ 2 := by
    have hγAt : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ u :=
      ((hGeo.1 u (hunit hu)).contMDiffAt (isOpen_Ioo.mem_nhds (hunit hu))).of_le (by norm_num)
    calc
      _ = actualPathSpeed (h a) β u ^ 2 := (actualPathSpeed_sq (h a) β u).symm
      _ = actualPathSpeed (h a) γ u ^ 2 :=
        (actualPathSpeed_sq_congr_eventuallyEq (h a) γ β u (hnearβ u hu) hγAt
          ((hβ u).of_le (by norm_num))).symm
      _ = _ := (actualPathSpeed_sq (h a) γ u).trans (hspeedγ u hu)
  exact ⟨δ, γ, β, hδ, hγ0, by simpa only [hγ1] using hy,
    by simpa only [hγ1] using hmin.symm, hGeo, hspeedγ, hβ, hβ0,
    by simpa only [hβ1] using hy, hnearβ, hspeedβ⟩

end Yau.NodeProofs.C01Aux

import Yau.Proofs.F01AllSpatialWordSchauder
import Yau.Proofs.F01NormalizedComplexSandwich
import Yau.Proofs.F01NativeSchauderEstimates

/-! All-order spatial Schauder bounds for the actual native potential.
Every profile, sandwich and word equation is constructed from the original
flow identities; constants precede all flows, centers and admissible scales. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem normalized_native_all_spatial_schauder
    (g : HermitianField M) (hg : MetricSmooth g) (A : BoundedChartFamily g)
    {C α β : ℝ} (hC : 1 ≤ C) (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) :
    ∃ K : ℕ → ℝ, (∀ k, 0 < K k) ∧
      ∀ k (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) (T ρ : ℝ),
      0 < ρ → 2 * ρ ≤ A.radius → 2 * ρ ≤ 1 → (2 * ρ) ^ 2 ≤ T →
      SmoothSpaceTime U (Icc 0 T) → h 0 = g → (∀ x, U x 0 = 0) →
      (∀ s ∈ Icc 0 T, ∀ x,
        gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x) →
      (∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
        (flowLogDetRatio g h x s) (Icc 0 T) s) →
      (∀ x s, s ∈ Icc 0 T →
        (gMat (h s) x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
        ((C : ℂ) • gMat g x - gMat (h s) x).PosSemidef) →
      ∀ (a : M.Carrier) (i : RIdx n) (vs : List (Space n)), NativeFrameWord vs → vs.length = k →
      SchauderBound (min α β) (cylinder (ball 0 (1 / 2)) (-(1 / 2)) (1 / 2))
        (spatialDerivativeWord vs (spatialDerivativeWord [realVec i]
          (forwardZeroSpaceTime (parabolicRescalePotential ρ
            (fun p : Point n => U (A.chart a p.1) p.2))))) (K k) := by
  classical
  let δ := min α β
  have hδ : 0 < δ := lt_min hα hβ
  have hδ1 : δ < 1 := (min_le_left α β).trans_lt hα1
  obtain ⟨Ci, hCi, hInitial⟩ := normalized_initial_schauder g hg A hC hα hα1 hβ hβ1
  obtain ⟨D, hD, hSandwich⟩ := normalized_native_complex_sandwich g hg A hC
  obtain ⟨Ks, hKs, hSjets⟩ := normalized_background_spatial_tensor_holder_budgets A hδ1.le
  obtain ⟨Kd, hKd, hDjets⟩ := normalizedPotentialLogSource_spatial_holder_budgets A hδ1.le
  let B : ℕ → ℝ := fun j => max (Ks j) (Kd j)
  have hB (j : ℕ) : 0 < B j := (hKs j).trans_le (le_max_left _ _)
  have each := all_spatial_word_schauder_budgets
    (Yau.LeafProofs.L12Aux.manifold_dimension_pos M) hδ hδ1 hD hCi.le B hB
  choose K hK hEst using each
  refine ⟨K, hK, ?_⟩
  intro k h U T ρ hρ hρr2 hρ12 hρT2 hU hh0 hU0 hpot hpde hflow a i vs hvs hlen
  have hρr : ρ ≤ A.radius := by linarith [hρ.le]
  have hρ1 : ρ ≤ 1 := by linarith [hρ.le]
  have hρT : ρ ^ 2 ≤ T := by nlinarith [sq_nonneg ρ]
  let u := parabolicRescalePotential ρ (fun p : Point n => U (A.chart a p.1) p.2)
  let V := forwardZeroSpaceTime u
  let S := normalizedComplexBackground A a ρ
  let d := normalizedPotentialLogSource A a ρ
  have hInit : SchauderBound δ (cylinder (ball 0 1) (-1) 1) V Ci :=
    hInitial h U T ρ hρ hρr2 hρ12 hρT2 hU hh0 hU0 hpot hpde hflow a
  have hData := normalized_rescale_initial_jet_data A h U hρ hρr hρT hU hh0 hU0 hpde a
  have hVs (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
      ContDiffOn ℝ ∞ (fun z => V (z, t)) (ball 0 1) :=
    forwardZeroSpaceTime_smooth_slices (fun s hs => contDiffOn_space_slice hData.1 hs) ht.2
  have hSj (j : ℕ) : HolderBound δ (cylinder (ball 0 1) (-1) 1)
      (fun p => iteratedFDeriv ℝ j (fun z => S (z, p.2)) p.1) (B j) :=
    holderBound_mono_const (hSjets j ρ hρ hρr hρ1 a) (le_max_left _ _)
  have hdj (j : ℕ) : HolderBound δ (cylinder (ball (0 : Space n) 1) (-1) 1)
      (fun p => iteratedFDeriv ℝ j d p.1) (B j) :=
    holderBound_mono_const (hDjets j ρ hρ hρr hρ1 a) (le_max_right _ _)
  have hPos : ∀ p ∈ cylinder (ball 0 1) (-1) 1, (chartPotentialMatrix S V p).PosDef :=
    fun p hp => normalized_chart_potential_pos hg A h U hρ hρr hρT hU hh0 hpot a hp
  have hBounds := hSandwich h U T ρ hρ hρr hρT hU hh0 hpot hflow a
  have hEq (i : RIdx n) : PotentialSpatialWordEquations S V d (realVec i) :=
    normalized_native_potential_word_equations hg A h U hρ hρr hρT hU hh0 hU0 hpot hpde a (realVec i)
  have hh := hEst k S V d hInit
    (fun t _ => normalizedComplexBackground_smooth_spatial_slice A hρ hρr a t)
    hVs (normalizedPotentialLogSource_smooth A hρ hρr a) hSj hdj hPos hBounds hEq i vs hvs hlen
  have hR := bootstrapRadius_bounds (k + 1)
  apply schauderBound_closed_cylinder_restrict (by norm_num : (-(1 / 2) : ℝ) < 1 / 2)
    (ball_subset_ball hR.1.le) (fun t ht => ⟨by linarith [ht.1], ht.2⟩) hh

end Yau.NodeProofs.F01Aux

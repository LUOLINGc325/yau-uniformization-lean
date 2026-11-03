import Yau.Proofs.F01BackwardNativeSchauder
import Yau.Proofs.F01ShiftedPotentialScale
import Yau.Proofs.F01AllBackwardSpatialSchauder

/-! All spatial orders of the same native potential are controlled on
a fixed backward core, up to every supplied final flow time. One positive
budget family precedes every flow, chart center and terminal clock. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem native_backward_all_spatial_schauder
    (g : HermitianField M) (hg : MetricSmooth g) (A : BoundedChartFamily g)
    {ρ Tcap C α β : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (hρ1 : ρ ≤ 1)
    (hTcap : 0 ≤ Tcap) (hC : 1 ≤ C) (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) :
    ∃ K : ℕ → ℝ, (∀ k, 0 < K k) ∧
      ∀ k (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) (T τ : ℝ),
      T ≤ Tcap → ρ ^ 2 ≤ τ → τ ≤ T →
      SmoothSpaceTime U (Icc 0 T) → (∀ x, U x 0 = 0) →
      (∀ s ∈ Icc 0 T, ∀ x,
        gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x) →
      (∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
        (flowLogDetRatio g h x s) (Icc 0 T) s) →
      (∀ x s, s ∈ Icc 0 T →
        (gMat (h s) x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
        ((C : ℂ) • gMat g x - gMat (h s) x).PosSemidef) →
      ∀ (a : M.Carrier) (i : RIdx n) (vs : List (Space n)), NativeFrameWord vs → vs.length = k →
      SchauderBound (min α β) (cylinder (ball 0 (1 / 2)) (-(1 / 2)) 0)
        (spatialDerivativeWord vs (spatialDerivativeWord [realVec i]
          (shiftedNativePotential A U a (ρ * (1 / 4)) τ))) (K k) := by
  classical
  let δ := min α β
  have hδ : 0 < δ := lt_min hα hβ
  have hδ1 : δ < 1 := (min_le_left α β).trans_lt hα1
  obtain ⟨Ci, hCi, hInitial⟩ := backward_native_schauder g hg A hρ hρr hρ1 hTcap hC hα hα1 hβ hβ1
  obtain ⟨D, hD, hMetric⟩ := dilated_native_metric_sandwich A hC
  obtain ⟨Ks, hKs, hSjets⟩ := shifted_background_spatial_tensor_holder_budgets A hTcap hδ1.le
  obtain ⟨Kd, hKd, hDjets⟩ := normalizedPotentialLogSource_spatial_holder_budgets A hδ1.le
  let B : ℕ → ℝ := fun j => max (Ks j) (Kd j)
  have hB (j : ℕ) : 0 < B j := (hKs j).trans_le (le_max_left _ _)
  have each := backward_spatial_word_schauder_budgets
    (Yau.LeafProofs.L12Aux.manifold_dimension_pos M) hδ hδ1 hD (by positivity : 0 ≤ 16 * Ci) B hB
  choose K hK hEst using each
  refine ⟨K, hK, ?_⟩
  intro k h U T τ hCap hLower hUpper hU hU0 hpot hpde hflow a i vs hvs hlen
  let σ : ℝ := ρ * (1 / 4)
  have hσ : 0 < σ := mul_pos hρ (by norm_num)
  have hσρ : σ ≤ ρ := by dsimp only [σ]; linarith [hρ.le]
  have hσr : σ ≤ A.radius := hσρ.trans hρr
  have hσ1 : σ ≤ 1 := hσρ.trans hρ1
  have hσLower : σ ^ 2 ≤ τ := by
    have hSq : σ ^ 2 ≤ ρ ^ 2 := by dsimp only [σ]; nlinarith [sq_nonneg ρ]
    exact hSq.trans hLower
  have hτ : |τ| ≤ Tcap := by
    rw [abs_of_nonneg (by nlinarith [sq_nonneg ρ] : 0 ≤ τ)]
    exact hUpper.trans hCap
  let V := shiftedNativePotential A U a σ τ
  let S := shiftedComplexBackground A a σ τ
  let d := normalizedPotentialLogSource A a σ
  have hInit : SchauderBound δ (cylinder (ball 0 1) (-1) 0) V (16 * Ci) :=
    shifted_native_quarter_schauder A U a ρ τ hδ.le
      (hInitial h U T τ hCap hLower hUpper hU hU0 hpot hpde hflow a)
  have hV := shifted_backward_native_potential_smooth A U hσ hσr hσLower hUpper hU a
  have hSub : cylinder (ball (0 : Space n) 1) (-1) 0 ⊆ cylinder (ball 0 1) (-1) 1 :=
    fun p hp => ⟨hp.1, hp.2.1, hp.2.2.trans zero_le_one⟩
  have hSj (j : ℕ) : HolderBound δ (cylinder (ball 0 1) (-1) 0)
      (fun p => iteratedFDeriv ℝ j (fun z => S (z, p.2)) p.1) (B j) :=
    holderBound_mono_const (holderBound_restrict (hSjets j σ τ hσ hσr hσ1 hτ a) hSub) (le_max_left _ _)
  have hdj (j : ℕ) : HolderBound δ (cylinder (ball (0 : Space n) 1) (-1) 0)
      (fun p => iteratedFDeriv ℝ j d p.1) (B j) :=
    holderBound_mono_const (holderBound_restrict (hDjets j σ hσ hσr hσ1 a) hSub) (le_max_right _ _)
  have hPos : ∀ p ∈ cylinder (ball 0 1) (-1) 0, (chartPotentialMatrix S V p).PosDef :=
    fun p hp => shifted_backward_native_matrix_pos hg A h U hσ hσr hσLower hUpper hU hpot a hp
  have hBounds : ∀ p ∈ cylinder (ball 0 1) (-1) 0,
      (chartPotentialMatrix S V p - ((D⁻¹ : ℝ) : ℂ) • 1).PosSemidef ∧
      ((D : ℂ) • 1 - chartPotentialMatrix S V p).PosSemidef := by
    intro p hp
    have ht := shifted_backward_clock_maps hσLower hUpper hp.2
    change (chartPotentialMatrix (shiftedComplexBackground A a σ τ) (shiftedNativePotential A U a σ τ) p -
      ((D⁻¹ : ℝ) : ℂ) • 1).PosSemidef ∧ _
    rw [shifted_native_flow_matrix_at hg A h U hσ.ne' hU hpot a p
      (spatialDilation_mem_ball hσ hσr hp.1) ht]
    simpa only [affineParabolicPoint, add_zero] using
      hMetric (h (affineParabolicPoint σ 0 τ p).2) σ hσ hσr (fun x => hflow x _ ht) a p.1 hp.1
  have hEq (j : RIdx n) : PotentialWordEquationsOn (cylinder (ball 0 1) (-1) 0) S V d (realVec j) :=
    shifted_backward_native_word_equations hg A h U hσ hσr hσLower hUpper hU hpot hpde a (realVec j)
  have hh := hEst k S V d hInit
    (fun t _ => shiftedComplexBackground_smooth_spatial_slice A hσ hσr τ a t)
    (fun t ht => contDiffOn_space_slice hV ht) (normalizedPotentialLogSource_smooth A hσ hσr a)
    hSj hdj hPos hBounds hEq i vs hvs hlen
  have hR := bootstrapRadius_bounds (k + 1)
  exact schauderBound_closed_cylinder_restrict (by norm_num : (-(1 / 2) : ℝ) < 0)
    (ball_subset_ball hR.1.le) (fun t ht => ⟨by linarith [ht.1], ht.2⟩) hh

end Yau.NodeProofs.F01Aux

import Yau.Proofs.F04GalerkinTimeIdentity
import Yau.Proofs.F04GalerkinFamilyEvolution
import Yau.Proofs.F04VariationalTimeFunctional

open MeasureTheory Filter Set TopologicalSpace
open scoped Topology InnerProductSpace ContDiff

noncomputable section

namespace Yau.F04Proof

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [SeparableSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem variationalGalerkin_time_test_of_mem
    {T C : ℝ} (hT : 0 < T) (hC : 0 ≤ C) (j : V →L[ℝ] H) (hj : Function.Injective j)
    (m : ℕ) (B : ℝ → V →L[ℝ] V →L[ℝ] ℝ)
    (hB : ∀ t, ‖B t‖ ≤ C) (hcB : ∀ u v, Continuous (fun t => B t u v))
    {F : ℝ → H} (hF : MemLp F 2 (volume.restrict (Ioo 0 T)))
    {c : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ (variationalGalerkinPivotSpace j m)))}
    (hc : ContinuousOn c (Icc 0 T))
    (hcEq : ∀ t ∈ Icc 0 T, c t = ∫ s in (0 : ℝ)..t,
      variationalForcing j (variationalGalerkinFamily j hj m) (F s) -
      variationalMatrix (variationalGalerkinFamily j hj m) (B s) (c s))
    {η : ℝ → ℝ} (hη : ContDiff ℝ 1 η) (hηT : η T = 0)
    {w : V} (hw : w ∈ variationalGalerkinSpace V m) :
    (∫ t in Ioo 0 T, -deriv η t * inner ℝ
      (j (variationalReconstruction (variationalGalerkinFamily j hj m) (c t))) (j w) +
      η t * B t (variationalReconstruction (variationalGalerkinFamily j hj m) (c t)) w) =
      ∫ t in Ioo 0 T, η t * inner ℝ (F t) (j w) := by
  obtain ⟨d, hd⟩ := variationalGalerkin_reconstruction_surjective j hj m hw
  have h := variationalGalerkin_time_test_identity hT hC j _
    (variationalGalerkinFamily_value_orthonormal j hj m) B hB hcB hF hc hcEq hη hηT d
  rw [hd] at h
  exact h

/-- Every actual finite-space test survives passage to its actual quotient
 representative. The original initial-retaining time tests are preserved. -/
theorem variationalGalerkin_classes_time_identity
    {T C : ℝ} (hT : 0 < T) (hC : 0 ≤ C) (j : V →L[ℝ] H) (hj : Function.Injective j)
    (B : ℝ → V →L[ℝ] V →L[ℝ] ℝ)
    (hB : ∀ t, ‖B t‖ ≤ C) (hcB : ∀ u v, Continuous (fun t => B t u v))
    {F : ℝ → H} (hF : MemLp F 2 (volume.restrict (Ioo 0 T)))
    (c : VariationalCoefficientFamily j) (hEvolution : VariationalGalerkinEvolution j hj B T F c)
    (classes : ℕ → Lp V 2 (volume.restrict (Ioo 0 T)))
    (hClasses : ∀ m, (classes m : ℝ → V) =ᵐ[volume.restrict (Ioo 0 T)]
      (fun t => variationalReconstruction (variationalGalerkinFamily j hj m) (c m t)))
    {η : ℝ → ℝ} (hη : ContDiff ℝ 1 η) (hηT : η T = 0) :
    ∀ m, ∀ w ∈ variationalGalerkinSpace V m,
      (∫ t in Ioo 0 T, -deriv η t * inner ℝ (j (classes m t)) (j w) +
        η t * B t (classes m t) w) = ∫ t in Ioo 0 T, η t * inner ℝ (F t) (j w) := by
  intro m w hw
  have hFinite := variationalGalerkin_time_test_of_mem hT hC j hj m B hB hcB hF
    (hEvolution m).1 (hEvolution m).2.2 hη hηT hw
  calc
    _ = ∫ t in Ioo 0 T, -deriv η t * inner ℝ
        (j (variationalReconstruction (variationalGalerkinFamily j hj m) (c m t))) (j w) +
        η t * B t (variationalReconstruction (variationalGalerkinFamily j hj m) (c m t)) w := by
      apply integral_congr_ae
      filter_upwards [hClasses m] with t ht
      rw [ht]
    _ = _ := hFinite

/-- Weak convergence passes each actual time test to the dense union of the
 original finite energy spaces, with no assertion of pointwise convergence. -/
theorem variational_weak_time_identity_on_union
    {T C : ℝ} (hC : 0 ≤ C) (j : V →L[ℝ] H)
    (B : ℝ → V →L[ℝ] V →L[ℝ] ℝ)
    (hB : ∀ t, ‖B t‖ ≤ C) (hcB : ∀ u v, Continuous (fun t => B t u v))
    (classes : ℕ → Lp V 2 (volume.restrict (Ioo 0 T))) (U : Lp V 2 (volume.restrict (Ioo 0 T)))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hWeak : ∀ ℓ : Lp V 2 (volume.restrict (Ioo 0 T)) →L[ℝ] ℝ,
      Tendsto (fun k => ℓ (classes (φ k))) atTop (𝓝 (ℓ U)))
    {η : ℝ → ℝ} (hη : ContDiff ℝ 1 η) (F : ℝ → H)
    (hStage : ∀ m, ∀ w ∈ variationalGalerkinSpace V m,
      (∫ t in Ioo 0 T, -deriv η t * inner ℝ (j (classes m t)) (j w) +
        η t * B t (classes m t) w) = ∫ t in Ioo 0 T, η t * inner ℝ (F t) (j w)) :
    ∀ w ∈ (⋃ m, (variationalGalerkinSpace V m : Set V)),
      (∫ t in Ioo 0 T, -deriv η t * inner ℝ (j (U t)) (j w) + η t * B t (U t) w) =
        ∫ t in Ioo 0 T, η t * inner ℝ (F t) (j w) := by
  have hηLp : MemLp η 2 (volume.restrict (Ioo 0 T)) := by
    rw [restrict_Ioo_eq_restrict_Icc]
    exact Yau.LeafProofs.L16HilbertTimeRegularization.continuousOn_memLp_two hη.continuous.continuousOn
  have hηDLp : MemLp (deriv η) 2 (volume.restrict (Ioo 0 T)) := by
    rw [restrict_Ioo_eq_restrict_Icc]
    exact Yau.LeafProofs.L16HilbertTimeRegularization.continuousOn_memLp_two
      hη.continuous_deriv_one.continuousOn
  intro w hw
  obtain ⟨m, hm⟩ := mem_iUnion.mp hw
  let ℓ := variationalWeakTimeFunctional B C hC hB hcB (volume.restrict (Ioo 0 T)) j hηLp hηDLp w
  have hConv := hWeak ℓ
  have hEv : ∀ᶠ k in atTop, ℓ (classes (φ k)) = ∫ t in Ioo 0 T, η t * inner ℝ (F t) (j w) := by
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop m)] with k hk
    rw [variationalWeakTimeFunctional_apply]
    exact hStage (φ k) w ((variationalGalerkinSpace_monotone V hk) hm)
  have hConst : Tendsto (fun k => ℓ (classes (φ k))) atTop
      (𝓝 (∫ t in Ioo 0 T, η t * inner ℝ (F t) (j w))) :=
    (tendsto_congr' hEv).mpr tendsto_const_nhds
  have h := tendsto_nhds_unique hConv hConst
  simpa only [ℓ, variationalWeakTimeFunctional_apply] using h

end Yau.F04Proof

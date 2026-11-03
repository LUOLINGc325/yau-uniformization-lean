import Yau.Proofs.F04GalerkinTraceBridge
import Yau.Proofs.F04TerminalScalarTests
import Yau.Proofs.F04CoerciveTraceBound

open MeasureTheory Filter Set TopologicalSpace
open scoped Topology InnerProductSpace ContDiff

noncomputable section

namespace Yau.F04Proof

/-- A genuine zero-initial variational evolution is constructed from a
 bounded continuous coercive form on the supplied Hilbert triple. This is a
 proved construction, with the quantitative constant preceding the source. -/
theorem coercive_variational_evolution_exists
    {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] [SeparableSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {T C α shift : ℝ} (hT : 0 < T) (hC : 0 ≤ C) (hα : 0 < α) (hshift : 0 ≤ shift)
    (j : V →L[ℝ] H) (hj : ‖j‖ ≤ 1) (hjinj : Function.Injective j) (hjd : DenseRange j)
    (B : ℝ → V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ t, ‖B t‖ ≤ C)
    (hcB : ∀ u v, Continuous (fun t => B t u v))
    (hGard : ∀ t ∈ Icc 0 T, ∀ v : V, α * ‖v‖ ^ 2 ≤ B t v v + shift * ‖j v‖ ^ 2) :
    ∃ E : ℝ, 0 < E ∧ ∀ F : ℝ → H, MemLp F 2 (volume.restrict (Ioo 0 T)) →
      ∃ (U : ℝ → V) (R : ℝ → StrongDual ℝ V) (a : ℝ → H),
        MemLp U 2 (volume.restrict (Ioo 0 T)) ∧ MemLp R 2 (volume.restrict (Ioo 0 T)) ∧
        ContinuousOn a (Icc 0 T) ∧ a 0 = 0 ∧
        (∀ᵐ t ∂volume.restrict (Ioo 0 T), a t = j (U t)) ∧
        (∀ v : V, ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ioo 0 T →
          (∫ t in Ioo 0 T, η t * R t v) = -(∫ t in Ioo 0 T, deriv η t * inner ℝ (a t) (j v))) ∧
        (∀ᵐ t ∂volume.restrict (Ioo 0 T), ∀ v : V, R t v + B t (U t) v = inner ℝ (F t) (j v)) ∧
        (∫ t in Ioo 0 T, ‖U t‖ ^ 2 + ‖R t‖ ^ 2) ≤ E * (∫ t in Ioo 0 T, ‖F t‖ ^ 2) ∧
        ∀ t ∈ Icc 0 T, ‖a t‖ ^ 2 ≤ E * (∫ s in Ioo 0 T, ‖F s‖ ^ 2) := by
  let KV := coerciveEnergyBound T (2 * α) (2 * shift + 1)
  let KH := coerciveTimeBound T (2 * shift + 1)
  let KR := 2 + 2 * C ^ 2 * KV
  have hKV : 0 < KV := by
    dsimp only [KV, coerciveEnergyBound, coerciveTimeBound]
    positivity
  have hKH : 0 < KH := Real.exp_pos _
  have hKR : 0 < KR := by dsimp only [KR]; positivity
  let E := 1 + KH + KV + KR
  have hE : 0 < E := by dsimp only [E]; positivity
  refine ⟨E, hE, ?_⟩
  intro F hF
  let ν := volume.restrict (Ioo 0 T)
  let Q := ∫ t in Ioo 0 T, ‖F t‖ ^ 2
  have hQ : 0 ≤ Q := integral_nonneg (fun _ => sq_nonneg _)
  obtain ⟨c, hEvolution, classes, hClasses, U, hUbound, φ, hφ, hWeak⟩ :=
    variational_Galerkin_weak_limit hT hC hα hshift j hjinj B hB hcB hGard hF
  let f : Lp H 2 ν := hF.toLp F
  have hfNorm : ‖f‖ ^ 2 = Q := by
    rw [bochner_l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [hF.coeFn_toLp] with t ht
    rw [ht]
  obtain ⟨R, hR, hRbound, hRtest⟩ := time_dual_residual_exists j hj B C hC hB hcB ν f U
  have hRtestActual : ∀ W : Lp V 2 ν,
      (∫ t, R t (W t) ∂ν) = (∫ t, inner ℝ (F t) (j (W t)) ∂ν) - ∫ t, B t (U t) (W t) ∂ν := by
    intro W
    rw [hRtest W]
    congr 1
    apply integral_congr_ae
    filter_upwards [hF.coeFn_toLp] with t ht
    rw [ht]
  have hEq := time_residual_equation_ae j B C hB hcB ν hF (Lp.memLp U) hR hRtestActual
  have hUnion : ∀ η : ℝ → ℝ, ContDiff ℝ 1 η → η T = 0 →
      ∀ v ∈ (⋃ m, (variationalGalerkinSpace V m : Set V)),
        (∫ t in Ioo 0 T, -deriv η t * inner ℝ (j (U t)) (j v) + η t * B t (U t) v) =
          ∫ t in Ioo 0 T, η t * inner ℝ (F t) (j v) := by
    intro η hη hηT
    exact variational_weak_time_identity_on_union hC j B hB hcB classes U φ hφ hWeak hη F
      (variationalGalerkin_classes_time_identity hT hC j hjinj B hB hcB hF c hEvolution classes hClasses hη hηT)
  have hw := variational_union_equation_weak_time hT j B hB hcB hF U hR hEq hUnion
  obtain ⟨a, ha, ha0, hAE, hChain, _hInc⟩ :=
    hilbert_terminal_weak_zero_trace j hj hjd hT (Lp.memLp U) hR hw
  have hScalar := hilbert_terminal_scalar_tests j hT (Lp.memLp U) hR hAE hw
  have hRquant : (∫ t in Ioo 0 T, ‖R t‖ ^ 2) ≤ KR * Q := by
    calc
      _ ≤ (‖f‖ + C * ‖U‖) ^ 2 := hRbound
      _ ≤ 2 * ‖f‖ ^ 2 + 2 * C ^ 2 * ‖U‖ ^ 2 := by nlinarith only [sq_nonneg (‖f‖ - C * ‖U‖)]
      _ ≤ 2 * Q + 2 * C ^ 2 * (KV * Q) := by
        rw [hfNorm]
        exact add_le_add (le_refl (2 * Q))
          (mul_le_mul_of_nonneg_left hUbound (by positivity : 0 ≤ 2 * C ^ 2))
      _ = KR * Q := by dsimp only [KR]; ring
  have hUint : (∫ t in Ioo 0 T, ‖U t‖ ^ 2) ≤ KV * Q := by
    rw [← bochner_l2_norm_sq_integral U]
    exact hUbound
  have hUi := (memLp_two_iff_integrable_sq_norm (Lp.memLp U).aestronglyMeasurable).mp (Lp.memLp U)
  have hRi := (memLp_two_iff_integrable_sq_norm hR.aestronglyMeasurable).mp hR
  have hSum : (∫ t in Ioo 0 T, ‖U t‖ ^ 2 + ‖R t‖ ^ 2) ≤ E * Q := by
    calc
      _ = (∫ t in Ioo 0 T, ‖U t‖ ^ 2) + ∫ t in Ioo 0 T, ‖R t‖ ^ 2 := integral_add hUi hRi
      _ ≤ KV * Q + KR * Q := add_le_add hUint hRquant
      _ = (KV + KR) * Q := by ring
      _ ≤ E * Q := mul_le_mul_of_nonneg_right (by dsimp only [E]; linarith only [hKH]) hQ
  have hTrace := coercive_trace_uniform_bound hT hα hshift j B hGard hF (Lp.memLp U) hR ha ha0 hAE hChain hEq
  refine ⟨U, R, a, Lp.memLp U, hR, ha, ha0, hAE.mono (fun _ ht => ht.symm), hScalar, hEq, hSum, ?_⟩
  intro t ht
  exact (hTrace t ht).trans (mul_le_mul_of_nonneg_right (by dsimp only [E]; linarith only [hKV, hKR]) hQ)

end Yau.F04Proof

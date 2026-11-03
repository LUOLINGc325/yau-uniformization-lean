import Yau.Proofs.F04RieszTimeDual
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

open MeasureTheory Filter Set TopologicalSpace
open scoped Topology InnerProductSpace ENNReal

noncomputable section

namespace Yau.F04Proof

open Yau.LeafProofs.L16LionsTimeTrace

/-- Every time-space test identity implies the actual equation on ONE a.e.
 set for ALL energy vectors. Countability is used only on a dense sequence. -/
theorem time_residual_equation_ae
    {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [SeparableSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (j : V →L[ℝ] H) (B : ℝ → V →L[ℝ] V →L[ℝ] ℝ)
    (C : ℝ) (hB : ∀ t, ‖B t‖ ≤ C) (hc : ∀ u v, Continuous (fun t => B t u v))
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    {F : ℝ → H} {U : ℝ → V} {R : ℝ → StrongDual ℝ V}
    (hF : MemLp F 2 ν) (hU : MemLp U 2 ν) (hR : MemLp R 2 ν)
    (hTest : ∀ W : Lp V 2 ν, (∫ t, R t (W t) ∂ν) =
      (∫ t, inner ℝ (F t) (j (W t)) ∂ν) - ∫ t, B t (U t) (W t) ∂ν) :
    ∀ᵐ t ∂ν, ∀ v : V, R t v + B t (U t) v = inner ℝ (F t) (j v) := by
  have hRi (v : V) : Integrable (fun t => R t v) ν :=
    (ContinuousLinearMap.apply ℝ ℝ v).integrable_comp (hR.integrable (by norm_num))
  have hBi (v : V) : Integrable (fun t => B t (U t) v) ν :=
    bounded_bilinear_time_integrable B C hB hc ν hU (memLp_const v)
  have hFi (v : V) : Integrable (fun t => inner ℝ (F t) (j v)) ν := by
    simpa only [innerSL_apply_apply, real_inner_comm (j v)] using
      (innerSL ℝ (j v)).integrable_comp (hF.integrable (by norm_num))
  have hAE (v : V) : ∀ᵐ t ∂ν, R t v + B t (U t) v - inner ℝ (F t) (j v) = 0 := by
    apply ((hRi v).add (hBi v) |>.sub (hFi v)).ae_eq_zero_of_forall_setIntegral_eq_zero
    intro E hE _hνE
    let w : ℝ → V := E.indicator (fun _ => v)
    have hw : MemLp w 2 ν := (memLp_const v).indicator hE.nullMeasurableSet
    let W := hw.toLp w
    have hI (L : ℝ → StrongDual ℝ V) :
        (∫ t, L t (W t) ∂ν) = ∫ t in E, L t v ∂ν := by
      calc
        _ = ∫ t, E.indicator (fun t => L t v) t ∂ν := by
          apply integral_congr_ae
          filter_upwards [hw.coeFn_toLp] with t ht
          change L t ((hw.toLp w) t) = _
          rw [ht]
          by_cases htE : t ∈ E <;> simp [w, htE]
        _ = _ := integral_indicator hE
    have he := hTest W
    change (∫ t, R t (W t) ∂ν) =
      (∫ t, hilbertPivot j (F t) (W t) ∂ν) - ∫ t, (B t (U t)) (W t) ∂ν at he
    rw [hI R, hI (fun t => hilbertPivot j (F t)), hI (fun t => B t (U t))] at he
    change (∫ t in E, R t v ∂ν) =
      (∫ t in E, inner ℝ (F t) (j v) ∂ν) - ∫ t in E, B t (U t) v ∂ν at he
    simp only [Pi.sub_apply, Pi.add_apply]
    have hiAdd := integral_add (μ := ν.restrict E) (hRi v).integrableOn (hBi v).integrableOn
    have hiSub := integral_sub (μ := ν.restrict E) ((hRi v).integrableOn.add (hBi v).integrableOn) (hFi v).integrableOn
    simp only [Pi.add_apply, Pi.sub_apply] at hiAdd hiSub
    linarith only [he, hiAdd, hiSub]
  have hCount : ∀ᵐ t ∂ν, ∀ k : ℕ,
      R t (denseSeq V k) + B t (U t) (denseSeq V k) - inner ℝ (F t) (j (denseSeq V k)) = 0 :=
    ae_all_iff.mpr (fun k => hAE (denseSeq V k))
  filter_upwards [hCount] with t ht
  let L : StrongDual ℝ V := R t + B t (U t) - hilbertPivot j (F t)
  have hL (v : V) : L v = 0 :=
    (denseRange_denseSeq V).induction_on v (isClosed_eq L.continuous continuous_const)
      (fun k => ht k)
  intro v
  have hv := hL v
  change R t v + B t (U t) v - inner ℝ (F t) (j v) = 0 at hv
  exact sub_eq_zero.mp hv

end Yau.F04Proof

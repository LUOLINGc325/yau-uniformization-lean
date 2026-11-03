import Yau.Proofs.C05OriginalIntrinsicHeatDecay

/-! One original good sequence carries every static and temporal datum used
by the finite Harnack rigidity argument. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff Matrix ComplexOrder
namespace Yau.Proofs.C05Aux
open Yau Blueprint C04Aux C04RescaledTubeAux Yau.LeafProofs
open Yau.Proofs.C05NormalizedScalarTimeEvolutionAux
variable {n : ℕ} {X : KahlerManifold n}
set_option backward.isDefEq.respectTransparency false

theorem original_good_sequence_with_rigidity_data (o : Pt X) (h : Flow X)
    (U P ρ : STF X) (hf : FlowStage X o h U P ρ)
    (hH : HarnackCompleteness X o h) (hW : RicciWindows X o h ρ) :
    ∃ tw : ℕ → ℝ, (∀ i, 0 < tw i) ∧ Tendsto tw atTop atTop ∧
      ∃ hRi : ∀ i, 0 < scalarCurvature (h (tw i)) o,
        ∃ lam : ℝ, 0 < lam ∧ ∃ b : ℝ, 0 < b ∧ ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧
          (∀ i, scalarCurvature (originalSequenceMetric o h tw hRi i) o = 1 ∧
            lam ≤ relMinEigenvalue (gMat (originalSequenceMetric o h tw hRi i) o)
              (ricci (originalSequenceMetric o h tw hRi i) o)) ∧
          Tendsto (fun i => scalarHarnackSum h o (tw i) /
            scalarCurvature (h (tw i)) o^2) atTop (𝓝 0) ∧
          Tendsto (fun i => deriv (originalHarnackMinimumProfile o h tw i) 0) atTop (𝓝 0) ∧
          Tendsto (fun i => intrinsicInverseEnergyHeatRemainder (originalSequenceMetric o h tw hRi i) o)
            atTop (𝓝 0) ∧
          (∀ i, 0 ≤ (tw i*scalarCurvature (h (tw i)) o)⁻¹) ∧
          (∀ᶠ i in atTop, (tw i*scalarCurvature (h (tw i)) o)⁻¹ ≤ K) ∧
          (∀ᶠ i in atTop, ∀ x ∈ distBall (originalSequenceMetric o h tw hRi i) o (2*b),
            (∀ j ≤ 6, scalarJetNorm (originalSequenceMetric o h tw hRi i)
              (scalarCurvature (originalSequenceMetric o h tw hRi i)) j x ≤ B) ∧
            (∀ j ≤ 6, realRicciJetNorm (originalSequenceMetric o h tw hRi i) j x ≤ B)) := by
  obtain ⟨tw,htw,htwinf,hRi,lam,hlam,hnorm,hdefect,hQt,hSt,hZt,θ,hθ,N,b,hb,B,hB,hjet⟩ :=
    original_good_sequence_with_time_decay o h U P ρ hf.1 hH hW
  let k := originalSequenceMetric o h tw hRi
  have hk (i : ℕ) : MetricSmooth (k i) := metricSmooth_scale _ (hRi i) (h (tw i))
    (L23Aux.metricFamilySmooth_slice h hf.1.1.2.1 (htw i).le)
  have ho (i : ℕ) {r : ℝ} (hr : 0 < r) : o ∈ distBall (k i) o r :=
    (L23Aux.mem_distBall_iff (k i) o o hr).mpr (by
      rw [L23Aux.inducedDistance_self (k i) (hk i)]; exact hr)
  have hstatic : ∀ᶠ i in atTop, ∀ x ∈ distBall (k i) o (2*b),
      (∀ j ≤ 6, scalarJetNorm (k i) (scalarCurvature (k i)) j x ≤ B) ∧
      (∀ j ≤ 6, realRicciJetNorm (k i) j x ≤ B) := by
    filter_upwards [eventually_ge_atTop N] with i hi
    have H := hjet i hi o (ho i zero_lt_one) 0 (by simpa only [abs_zero] using hθ)
    obtain ⟨_,_,_,_,Hjets⟩ := H
    simpa only [normalizedMetric,zero_div,add_zero,k,originalSequenceMetric] using Hjets
  have hcenter : ∀ᶠ i in atTop,
      (∀ j ≤ 6, scalarJetNorm (k i) (scalarCurvature (k i)) j o ≤ B) ∧
      (∀ j ≤ 4, realRicciJetNorm (k i) j o ≤ B) := by
    filter_upwards [hstatic] with i hi
    exact ⟨(hi o (ho i (by positivity : 0<2*b))).1,
      fun j hj => (hi o (ho i (by positivity : 0<2*b))).2 j (by omega)⟩
  have hE := original_sequence_heatRemainder_tendsto_zero o h U P ρ hf.1 hH tw htw hRi
    hlam hB.le (fun i => (hnorm i).2) hdefect hcenter
  obtain ⟨δ,hδ,hδθ,K,hK,hclock⟩ :=
    eventual_original_normalized_clock_control o h U P ρ hf.1 hH tw htwinf hRi hθ
  have hκ (i : ℕ) : 0 ≤ (tw i*scalarCurvature (h (tw i)) o)⁻¹ :=
    inv_nonneg.mpr (mul_nonneg (htw i).le (hRi i).le)
  have hcap : ∀ᶠ i in atTop, (tw i*scalarCurvature (h (tw i)) o)⁻¹ ≤ K := by
    filter_upwards [hclock] with i hi
    have H := (hi 0 (by simpa only [abs_zero] using hδ)).2
    simpa only [add_zero,abs_of_nonneg (hκ i)] using H
  exact ⟨tw,htw,htwinf,hRi,lam,hlam,b,hb,B,hB,K,hK,hnorm,hdefect,hZt,hE,hκ,hcap,hstatic⟩

end Yau.Proofs.C05Aux

import Yau.Proofs.C05OriginalInverseEnergyTimeDecay
import Yau.Proofs.C05OriginalScalarHarnackTimeDecay
import Yau.Proofs.C05OriginalNormalizedClock

/-! All temporal near-minimum conclusions are now consequences of the
original flow and its original RicciWindows sequence, without added budgets. -/
noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff Matrix ComplexOrder
namespace Yau.Proofs.C05Aux
open Yau Blueprint C04Aux C04RescaledTubeAux Yau.LeafProofs
open Yau.Proofs.C05NormalizedScalarTimeEvolutionAux
variable {n : ℕ} {X : KahlerManifold n}
set_option backward.isDefEq.respectTransparency false

def originalScalarHarnackProfile (o : Pt X) (h : Flow X) (tw : ℕ → ℝ)
    (hRi : ∀ i, 0 < scalarCurvature (h (tw i)) o) (i : ℕ) (z : ℝ) : ℝ :=
  scalarHarnackSource (normalizedMetric h (tw i) (scalarCurvature (h (tw i)) o) (hRi i) z)
    (tw i*scalarCurvature (h (tw i)) o+z)⁻¹ o

def originalInverseEnergyProfile (o : Pt X) (h : Flow X) (tw : ℕ → ℝ)
    (hRi : ∀ i, 0 < scalarCurvature (h (tw i)) o) (i : ℕ) (z : ℝ) : ℝ :=
  realRicciDifferentialEnergy (normalizedMetric h (tw i) (scalarCurvature (h (tw i)) o) (hRi i) z)
    (scalarCurvature (normalizedMetric h (tw i) (scalarCurvature (h (tw i)) o) (hRi i) z)) o

def originalHarnackMinimumProfile (o : Pt X) (h : Flow X) (tw : ℕ → ℝ)
    (i : ℕ) (z : ℝ) : ℝ :=
  normalizedHarnackMinimum h (tw i) (scalarCurvature (h (tw i)) o) o z

theorem original_good_sequence_with_time_decay (o : Pt X) (h : Flow X)
    (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) (hW : RicciWindows X o h ρ) :
    ∃ tw : ℕ → ℝ, (∀ i, 0 < tw i) ∧ Tendsto tw atTop atTop ∧
      ∃ hRi : ∀ i, 0 < scalarCurvature (h (tw i)) o,
        ∃ lam : ℝ, 0 < lam ∧
          (∀ i, scalarCurvature (originalSequenceMetric o h tw hRi i) o = 1 ∧
            lam ≤ relMinEigenvalue (gMat (originalSequenceMetric o h tw hRi i) o)
              (ricci (originalSequenceMetric o h tw hRi i) o)) ∧
          Tendsto (fun i => scalarHarnackSum h o (tw i) /
            scalarCurvature (h (tw i)) o^2) atTop (𝓝 0) ∧
          Tendsto (fun i => deriv (originalInverseEnergyProfile o h tw hRi i) 0) atTop (𝓝 0) ∧
          Tendsto (fun i => deriv (originalScalarHarnackProfile o h tw hRi i) 0) atTop (𝓝 0) ∧
          Tendsto (fun i => deriv (originalHarnackMinimumProfile o h tw i) 0) atTop (𝓝 0) ∧
          ∃ θ : ℝ, 0 < θ ∧ ∃ N : ℕ, ∃ b : ℝ, 0 < b ∧ ∃ B : ℝ, 0 < B ∧
            ∀ i : ℕ, N ≤ i → ∀ p ∈ distBall (originalSequenceMetric o h tw hRi i) o 1,
              ∀ z : ℝ, |z| < θ →
                let k := normalizedMetric h (tw i) (scalarCurvature (h (tw i)) o) (hRi i) z
                0 < tw i+z/scalarCurvature (h (tw i)) o ∧ MetricSmooth k ∧ KahlerClosed k ∧
                  IsCompleteDistance (lengthDist k) ∧ ∀ x ∈ distBall k p (2*b),
                    (∀ m ≤ 6, scalarJetNorm k (scalarCurvature k) m x ≤ B) ∧
                    (∀ m ≤ 6, realRicciJetNorm k m x ≤ B) := by
  obtain ⟨tw,htw,htwinf,hRi,lam,hlam,hnorm,hdefect,θ,hθ,N,b,hb,B,hB,hjet⟩ :=
    original_good_sequence_with_finite_jet_tubes o h U P ρ hf hH hW
  have hk0 (i : ℕ) : MetricSmooth (originalSequenceMetric o h tw hRi i) :=
    metricSmooth_scale _ (hRi i) (h (tw i)) (L23Aux.metricFamilySmooth_slice h hf.1.2.1 (htw i).le)
  have hcenter : ∀ᶠ i in atTop, ∀ z : ℝ, |z| < θ →
      0 < tw i+z/scalarCurvature (h (tw i)) o ∧
      (∀ j ≤ 6, scalarJetNorm (normalizedMetric h (tw i) (scalarCurvature (h (tw i)) o) (hRi i) z)
        (scalarCurvature (normalizedMetric h (tw i) (scalarCurvature (h (tw i)) o) (hRi i) z)) j o ≤ B) ∧
      (∀ j ≤ 4, realRicciJetNorm (normalizedMetric h (tw i) (scalarCurvature (h (tw i)) o) (hRi i) z) j o ≤ B) := by
    filter_upwards [eventually_ge_atTop N] with i hi
    intro z hz
    have hp : o ∈ distBall (originalSequenceMetric o h tw hRi i) o 1 :=
      (L23Aux.mem_distBall_iff _ o o zero_lt_one).mpr (by
        rw [L23Aux.inducedDistance_self _ (hk0 i)]; norm_num)
    obtain ⟨ht,hk,hK,hcomplete,hjets⟩ := hjet i hi o hp z hz
    have hx : o ∈ distBall (normalizedMetric h (tw i) (scalarCurvature (h (tw i)) o) (hRi i) z) o (2*b) :=
      (L23Aux.mem_distBall_iff _ o o (by positivity : 0<2*b)).mpr (by
        rw [L23Aux.inducedDistance_self
          (normalizedMetric h (tw i) (scalarCurvature (h (tw i)) o) (hRi i) z) hk o]; positivity)
    exact ⟨ht,(hjets o hx).1,fun j hj => (hjets o hx).2 j (by omega)⟩
  have hcenter0 : ∀ᶠ i in atTop,
      (∀ j ≤ 6, scalarJetNorm (originalSequenceMetric o h tw hRi i)
        (scalarCurvature (originalSequenceMetric o h tw hRi i)) j o ≤ B) ∧
      (∀ j ≤ 4, realRicciJetNorm (originalSequenceMetric o h tw hRi i) j o ≤ B) := by
    filter_upwards [hcenter] with i hi
    have H := (hi 0 (by simpa only [abs_zero] using hθ)).2
    simpa only [normalizedMetric,zero_div,add_zero,originalSequenceMetric] using H
  have hQt := (original_sequence_inverseEnergyTime_decay o h U P ρ hf hH tw htw hRi
    hlam hB.le (fun i => (hnorm i).2) hdefect hcenter0).2
  obtain ⟨δ,hδ,hδθ,K,hK,hclock⟩ :=
    eventual_original_normalized_clock_control o h U P ρ hf hH tw htwinf hRi hθ
  have hwindow : ∀ᶠ i in atTop, ∀ z : ℝ, |z| < δ →
      0 < tw i+z/scalarCurvature (h (tw i)) o ∧
      |(tw i*scalarCurvature (h (tw i)) o+z)⁻¹| ≤ K ∧
      (∀ j ≤ 6, scalarJetNorm (normalizedMetric h (tw i) (scalarCurvature (h (tw i)) o) (hRi i) z)
        (scalarCurvature (normalizedMetric h (tw i) (scalarCurvature (h (tw i)) o) (hRi i) z)) j o ≤ B) ∧
      (∀ j ≤ 4, realRicciJetNorm (normalizedMetric h (tw i) (scalarCurvature (h (tw i)) o) (hRi i) z) j o ≤ B) := by
    filter_upwards [hcenter,hclock] with i hi hc
    intro z hz
    exact ⟨(hc z hz).1,(hc z hz).2,(hi z (hz.trans hδθ)).2⟩
  have hSt := original_sequence_scalarHarnack_time_decay o h U P ρ hf hH tw htw hRi
    hδ hB.le hK.le hdefect hwindow
  have hZt : Tendsto (fun i => deriv (originalHarnackMinimumProfile o h tw i) 0) atTop (𝓝 0) := by
    have hs := hSt.sub hQt
    simp only [sub_zero] at hs
    apply hs.congr'
    apply Eventually.of_forall
    intro i
    have ht : 0 < tw i+0/scalarCurvature (h (tw i)) o := by simpa only [zero_div,add_zero] using htw i
    change _ - _ = deriv (originalHarnackMinimumProfile o h tw i) 0
    have he : originalHarnackMinimumProfile o h tw i =
        (fun z => normalizedHarnackMinimum h (tw i) (scalarCurvature (h (tw i)) o) o z) := rfl
    rw [he]
    rw [(normalized_minimum_hasDerivAt o h U P ρ hf hH (tw i)
      (scalarCurvature (h (tw i)) o) (hRi i) o 0 ht).deriv,
      (normalized_scalarHarnack_hasDerivAt o h U P ρ hf (tw i)
        (scalarCurvature (h (tw i)) o) (hRi i) o 0 ht).deriv,
      (normalized_inverseEnergy_hasDerivAt o h U P ρ hf hH (tw i)
        (scalarCurvature (h (tw i)) o) (hRi i) o 0 ht).deriv]
  exact ⟨tw,htw,htwinf,hRi,lam,hlam,hnorm,hdefect,hQt,hSt,hZt,θ,hθ,N,b,hb,B,hB,hjet⟩

end Yau.Proofs.C05Aux

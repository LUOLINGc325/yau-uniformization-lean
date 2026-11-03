import Yau.Proofs.C03EnergyParallelJets
import Yau.Proofs.C03SourceEnergyVariation

/-! The polynomial family supplies actual parallel first jets and a zero
covariant acceleration trace on both moving ends. -/

noncomputable section
open Filter Set
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

def movingJoint (γ W : ℝ → ComplexVector n) (Q : ComplexVector n)
    (p : ℂ × ℝ) : ComplexVector n := movingTrial γ W Q p.2 p.1

theorem movingJoint_contDiffOn (γ W : ℝ → ComplexVector n) (Q : ComplexVector n)
    (J : Set ℝ) (hγ : ContDiffOn ℝ 3 γ J) (hW : ContDiffOn ℝ 3 W J) :
    ContDiffOn ℝ 3 (movingJoint γ W Q) (univ ×ˢ J) :=
  (movingTrial_contDiffOn_order γ W Q J 3 hγ hW).comp
    (contDiffOn_snd.prodMk contDiffOn_fst) (fun _ hp => ⟨hp.2, mem_univ _⟩)

theorem movingJoint_parameter_jet (γ W : ℝ → ComplexVector n) (Q : ComplexVector n)
    {a : ℂ} {t : ℝ} (hZ : DifferentiableAt ℝ (movingJoint γ W Q) (a, t)) (v : ℂ) :
    mapDirection (movingJoint γ W Q) (v, 0) (a, t) =
      v • (W t + ((t : ℂ) * a) • Q) := by
  rw [mapDirection_parameter _ hZ]
  exact movingTrial_mapDirection γ W Q t a v

theorem movingJoint_time_jet_zero (γ W : ℝ → ComplexVector n) (Q : ComplexVector n)
    {t : ℝ} (hZ : DifferentiableAt ℝ (movingJoint γ W Q) (0, t)) :
    mapDirection (movingJoint γ W Q) (0, 1) (0, t) = deriv γ t := by
  rw [mapDirection_time _ hZ]
  have heq : (fun s => movingJoint γ W Q (0, s)) = γ := by
    funext s
    exact movingTrial_zero_parameter γ W Q s
  rw [heq]

theorem movingJoint_parallel_firstVariation
    (Γ : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (γ W : ℝ → ComplexVector n) (Q : ComplexVector n) {t : ℝ}
    (hZ : ContDiffAt ℝ 2 (movingJoint γ W Q) (0, t)) (a : ℂ)
    (hW : HasDerivAt (fun s => a • W s) (-Γ (γ t) (deriv γ t) (a • W t)) t) :
    mapCovariantD Γ (movingJoint γ W Q) (0, 1)
      (mapDirection (movingJoint γ W Q) (a, 0)) (0, t) = 0 := by
  have hjet : (fun s => mapDirection (movingJoint γ W Q) (a, 0) (0, s)) =ᶠ[𝓝 t]
      (fun s => a • W s) := by
    have H : ∀ᶠ s in 𝓝 t, ContDiffAt ℝ 1 (movingJoint γ W Q) (0, s) :=
      (continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds
        ((hZ.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).eventually (by norm_num))
    filter_upwards [H] with s hs
    rw [movingJoint_parameter_jet _ _ _ hs.differentiableAt_one]
    simp only [mul_zero, zero_smul, add_zero]
  apply mapCovariantD_unscaled_parallelVariation Γ _ hZ (fun s => a • W s) a _ hjet
  simpa only [movingJoint, movingTrial_zero_parameter,
    movingJoint_time_jet_zero γ W Q (hZ.differentiableAt (by norm_num))] using hW

theorem movingJoint_radial_covariant_trace
    (Γ : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (γ W : ℝ → ComplexVector n) (Q : ComplexVector n) {p : ℂ × ℝ}
    (hZ : ContDiffAt ℝ 2 (movingJoint γ W Q) p)
    (hI : ∀ v, Γ (movingJoint γ W Q p) (Complex.I • v) (Complex.I • v) =
      -Γ (movingJoint γ W Q p) v v) :
    mapCovariantD Γ (movingJoint γ W Q) (1, 0)
        (mapDirection (movingJoint γ W Q) (1, 0)) p +
      mapCovariantD Γ (movingJoint γ W Q) (Complex.I, 0)
        (mapDirection (movingJoint γ W Q) (Complex.I, 0)) p = 0 := by
  apply map_radial_pair_zero_of_connection_I Γ _ p hI
  · rw [movingJoint_parameter_jet _ _ _ (hZ.differentiableAt (by norm_num)),
      movingJoint_parameter_jet _ _ _ (hZ.differentiableAt (by norm_num))]
    simp only [one_smul]
  · rw [mapDirection_parameter_second _ hZ, mapDirection_parameter_second _ hZ]
    exact movingTrial_radial_trace_zero γ W Q p.2 p.1

end Yau.Proofs.C03Aux

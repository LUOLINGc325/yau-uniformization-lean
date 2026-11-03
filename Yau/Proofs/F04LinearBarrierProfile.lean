import Yau.Proofs.F04FlowRhoLp
import Yau.Proofs.F04CompactDifferentialProfiles
import Yau.Proofs.F03ScalarL2Pairing

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint Yau.Proofs.F03Aux Yau.LeafProofs.L03

/-- The actual spatially constant barrier M*t has genuine clamped pivot
 and form profiles, continuous in their actual norms, and the true
 one-sided closed-time L2 derivative. -/
theorem linear_barrier_L2_profiles
    {n : ℕ} {N : ComplexManifold n} (g : SmoothMetric N)
    (μ : Measure N.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω K : Set N.Carrier) (hΩ : MeasurableSet Ω) (hK : IsCompact K) (hΩK : Ω ⊆ K)
    {S M : ℝ} (hS : 0 < S) (hM : 0 ≤ M) :
    ∃ hf : ∀ t, MemLp (fun _ : N.Carrier => M * timeClamp S hS.le t) 2 (μ.restrict Ω),
    ∃ hd : ∀ t : ℝ, MemLp (fun _ : N.Carrier => M) 2 (μ.restrict Ω),
      Continuous (fun t => (hf t).toLp (fun _ => M * timeClamp S hS.le t)) ∧
      ContDiffOn ℝ 1 (fun t => (hf t).toLp (fun _ => M * timeClamp S hS.le t)) (Icc 0 S) ∧
      (∀ t ∈ Icc 0 S,
        HasDerivWithinAt (fun s => (hf s).toLp (fun _ => M * timeClamp S hS.le s))
          ((hd t).toLp (fun _ => M)) (Icc 0 S) t) ∧
      ∃ hD : ∀ t, L2RealForm g.form (μ.restrict Ω)
        (scalarExterior (fun _ => M * timeClamp S hS.le t)),
        Continuous (fun t => realizeL2Form g (μ.restrict Ω)
          (L2FormSpace.ofSection (scalarExterior (fun _ => M * timeClamp S hS.le t)) (hD t))) := by
  let := Yau.LeafProofs.L18Aux.riemannianVolume_locallyFinite g μ hμ
  let : IsFiniteMeasure (μ.restrict Ω) := ⟨by
    simpa only [Measure.restrict_apply_univ] using (lt_of_le_of_lt (measure_mono hΩK) hK.measure_lt_top)⟩
  have hSmooth : SmoothSpaceTime (fun _ : N.Carrier => fun t => M*t) (Icc 0 S) :=
    fun _ => contDiffOn_const.mul contDiffOn_snd
  obtain ⟨hf,hfc⟩ := compact_scalar_profile_L2 g μ hμ Ω K hΩ hK hΩK hS.le
    (fun _ t => M*t) (smoothSpaceTime_continuousOn hSmooth)
  let hd : ∀ t : ℝ, MemLp (fun _ : N.Carrier => M) 2 (μ.restrict Ω) := fun _ => memLp_const M
  have hder : ∀ᵐ x ∂μ.restrict Ω, ∀ t ∈ Icc 0 S,
      HasDerivWithinAt (fun s => M*timeClamp S hS.le s) M (Icc 0 S) t := by
    apply ae_of_all
    intro x t ht
    have he : EqOn (fun s => M*timeClamp S hS.le s) (fun s => M*s) (Icc 0 S) :=
      fun s hs => congrArg (fun r => M*r) (timeClamp_eq_of_mem S hS.le hs)
    have hh : HasDerivWithinAt (fun s : ℝ => M*s) M (Icc 0 S) t := by
      simpa only [id_eq,mul_one] using ((hasDerivAt_id t).const_mul M).hasDerivWithinAt
    exact hh.congr_of_mem he ht
  have hdb : ∀ᵐ x ∂μ.restrict Ω, ∀ t ∈ Icc 0 S, ‖M‖ ≤ M :=
    ae_of_all _ (fun _ _ _ => (Real.norm_of_nonneg hM).le)
  have hdc : ∀ᵐ x ∂μ.restrict Ω, ContinuousOn (fun _ : ℝ => M) (Icc 0 S) :=
    ae_of_all _ (fun _ => continuousOn_const)
  have hC1 := finiteLpCurve_contDiffOn_one (μ.restrict Ω)
    (fun t _ => M*timeClamp S hS.le t) (fun _ _ => M) hf hd hS M hM hder hdb hdc
  obtain ⟨hD,hDc⟩ := compact_scalar_differential_profile_L2 g μ hμ Ω K hΩ hK hΩK hS
    (fun _ t => M*t) hSmooth
  exact ⟨hf,hd,hfc,hC1,finiteLpCurve_hasDerivWithinAt (μ.restrict Ω)
    (fun t _ => M*timeClamp S hS.le t) (fun _ _ => M) hf hd hS M hM hder hdb,hD,hDc⟩

end Yau.F04Proof

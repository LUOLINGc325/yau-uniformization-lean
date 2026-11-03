import Yau.Proofs.F04SmoothPhysicalTime
import Yau.Proofs.F04CompactDifferentialProfiles
import Yau.Proofs.F04FiniteLpCurve

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint Yau.Proofs.F03Aux Yau.LeafProofs.L03

/-- A genuine globally smooth closed physical profile gives its actual
 clamped pivot C1 curve, true closed-time Banach derivative, and continuous
 completed spatial differential. Every derivative and L2 bound is produced
 internally from that profile and compact physical volume. -/
theorem compact_smooth_scalar_L2_profiles
    {n : ℕ} {M : ComplexManifold n} (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω K : Set M.Carrier) (hΩ : MeasurableSet Ω) (hK : IsCompact K) (hΩK : Ω ⊆ K)
    {S : ℝ} (hS : 0 < S) (v : M.Carrier → ℝ → ℝ) (hv : SmoothSpaceTime v (Icc 0 S)) :
    ∃ hf : ∀ t, MemLp (fun x => v x (timeClamp S hS.le t)) 2 (μ.restrict Ω),
    ∃ hd : ∀ t, MemLp (fun x => derivWithin (v x) (Icc 0 S) (timeClamp S hS.le t)) 2 (μ.restrict Ω),
      Continuous (fun t => (hf t).toLp (fun x => v x (timeClamp S hS.le t))) ∧
      Continuous (fun t => (hd t).toLp (fun x => derivWithin (v x) (Icc 0 S) (timeClamp S hS.le t))) ∧
      ContDiffOn ℝ 1 (fun t => (hf t).toLp (fun x => v x (timeClamp S hS.le t))) (Icc 0 S) ∧
      (∀ t ∈ Icc 0 S,
        HasDerivWithinAt (fun s => (hf s).toLp (fun x => v x (timeClamp S hS.le s)))
          ((hd t).toLp (fun x => derivWithin (v x) (Icc 0 S) (timeClamp S hS.le t))) (Icc 0 S) t) ∧
      ∃ hD : ∀ t, L2RealForm g.form (μ.restrict Ω)
        (scalarExterior (fun x => v x (timeClamp S hS.le t))),
        Continuous (fun t => realizeL2Form g (μ.restrict Ω)
          (L2FormSpace.ofSection (scalarExterior (fun x => v x (timeClamp S hS.le t))) (hD t))) := by
  let := Yau.LeafProofs.L18Aux.riemannianVolume_locallyFinite g μ hμ
  let : IsFiniteMeasure (μ.restrict Ω) := ⟨by
    simpa only [Measure.restrict_apply_univ] using (lt_of_le_of_lt (measure_mono hΩK) hK.measure_lt_top)⟩
  let d := fun x t => derivWithin (v x) (Icc 0 S) t
  have hDc := smoothSpaceTime_continuousOn (smoothSpaceTime_timeDerivative_smooth hS hv)
  obtain ⟨hf,hfc⟩ := compact_scalar_profile_L2 g μ hμ Ω K hΩ hK hΩK hS.le v (smoothSpaceTime_continuousOn hv)
  obtain ⟨hd,hdc⟩ := compact_scalar_profile_L2 g μ hμ Ω K hΩ hK hΩK hS.le d hDc
  obtain ⟨C,hC,hCb⟩ := compact_scalar_profile_bound hS.le d hDc K hK
  have hder : ∀ᵐ x ∂μ.restrict Ω, ∀ t ∈ Icc 0 S,
      HasDerivWithinAt (fun s => v x (timeClamp S hS.le s)) (d x (timeClamp S hS.le t)) (Icc 0 S) t := by
    apply ae_of_all
    intro x t ht
    have he : EqOn (fun s => v x (timeClamp S hS.le s)) (v x) (Icc 0 S) :=
      fun s hs => congrArg (v x) (timeClamp_eq_of_mem S hS.le hs)
    have hh := (smoothSpaceTime_hasDerivWithinAt hv x t ht).congr_of_mem he ht
    simpa only [d,timeClamp_eq_of_mem S hS.le ht] using hh
  have hdb : ∀ᵐ x ∂μ.restrict Ω, ∀ t ∈ Icc 0 S, ‖d x (timeClamp S hS.le t)‖ ≤ C := by
    filter_upwards [ae_restrict_mem hΩ] with x hx
    exact fun t _ => hCb x (hΩK hx) t
  have hdcx : ∀ᵐ x ∂μ.restrict Ω, ContinuousOn (fun t => d x (timeClamp S hS.le t)) (Icc 0 S) := by
    apply ae_of_all
    intro x
    exact (hDc.comp_continuous (continuous_const.prodMk (continuous_timeClamp S hS.le))
      (fun t => ⟨mem_univ x,timeClamp_mem S hS.le t⟩)).continuousOn
  have hC1 := finiteLpCurve_contDiffOn_one (μ.restrict Ω)
    (fun t x => v x (timeClamp S hS.le t)) (fun t x => d x (timeClamp S hS.le t))
    hf hd hS C hC hder hdb hdcx
  obtain ⟨hD,hRD⟩ := compact_scalar_differential_profile_L2 g μ hμ Ω K hΩ hK hΩK hS v hv
  exact ⟨hf,hd,hfc,hdc,hC1,finiteLpCurve_hasDerivWithinAt (μ.restrict Ω)
    (fun t x => v x (timeClamp S hS.le t)) (fun t x => d x (timeClamp S hS.le t))
    hf hd hS C hC hder hdb,hD,hRD⟩

end Yau.F04Proof

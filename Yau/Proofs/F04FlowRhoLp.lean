import Yau.Proofs.F04CompactLpProfiles
import Yau.Proofs.F04FiniteLpCurve

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace ENNReal

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

variable {n : ℕ}

/-- The supplied flow itself produces the actual clamped rho/R L2 profiles,
their true closed-time Banach derivative, and the original zero initial value. -/
theorem flow_rho_L2_profiles
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O K : Set (Pt X)) (hO : MeasurableSet O) (hK : IsCompact K) (hOK : O ⊆ K)
    {S : ℝ} (hS : 0 < S) :
    ∃ hf : ∀ t : ℝ, MemLp (fun x => ρ x (timeClamp S hS.le t)) 2 (μ.restrict O),
    ∃ hd : ∀ t : ℝ, MemLp (fun x => scalarCurvature (h (timeClamp S hS.le t)) x) 2 (μ.restrict O),
      Continuous (fun t => (hf t).toLp (fun x => ρ x (timeClamp S hS.le t))) ∧
      Continuous (fun t => (hd t).toLp (fun x => scalarCurvature (h (timeClamp S hS.le t)) x)) ∧
      ContDiffOn ℝ 1 (fun t => (hf t).toLp (fun x => ρ x (timeClamp S hS.le t))) (Icc 0 S) ∧
      (hf 0).toLp (fun x => ρ x (timeClamp S hS.le 0)) = 0 ∧
      ∀ t ∈ Icc 0 S,
        HasDerivWithinAt (fun s => (hf s).toLp (fun x => ρ x (timeClamp S hS.le s)))
          ((hd t).toLp (fun x => scalarCurvature (h (timeClamp S hS.le t)) x)) (Icc 0 S) t := by
  let := Yau.LeafProofs.L18Aux.riemannianVolume_locallyFinite X.metric μ hμ
  let : IsFiniteMeasure (μ.restrict O) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      (lt_of_le_of_lt (measure_mono hOK) hK.measure_lt_top)⟩
  have hρ : SmoothSpaceTime ρ (Icc 0 S) := fun c => (hloc.2.2.2.1 c).mono
    (prod_mono (Subset.refl _) (fun _ ht => ht.1))
  have hρc := smoothSpaceTime_continuousOn hρ
  have hRc := flow_scalarCurvature_continuousOn_closed X o h U P ρ hloc hS
  obtain ⟨hf, hfc⟩ := compact_scalar_profile_L2 X.metric μ hμ O K hO hK hOK hS.le ρ hρc
  obtain ⟨hd, hdc⟩ := compact_scalar_profile_L2 X.metric μ hμ O K hO hK hOK hS.le
    (fun x t => scalarCurvature (h t) x) hRc
  obtain ⟨C, hC, hCb⟩ := compact_scalar_profile_bound hS.le
    (fun x t => scalarCurvature (h t) x) hRc K hK
  have hder : ∀ᵐ x ∂μ.restrict O, ∀ t ∈ Icc 0 S,
      HasDerivWithinAt (fun s => ρ x (timeClamp S hS.le s))
        (scalarCurvature (h (timeClamp S hS.le t)) x) (Icc 0 S) t := by
    apply ae_of_all
    intro x t ht
    have heq : EqOn (fun s => ρ x (timeClamp S hS.le s)) (ρ x) (Icc 0 S) :=
      fun s hs => congrArg (ρ x) (timeClamp_eq_of_mem S hS.le hs)
    have hdρ := (rho_hasDerivWithinAt_Icc o h U P ρ hloc S x t ht).congr_of_mem heq ht
    simpa only [timeClamp_eq_of_mem S hS.le ht] using hdρ
  have hdb : ∀ᵐ x ∂μ.restrict O, ∀ t ∈ Icc 0 S,
      ‖scalarCurvature (h (timeClamp S hS.le t)) x‖ ≤ C := by
    filter_upwards [ae_restrict_mem hO] with x hx
    exact fun t _ => hCb x (hOK hx) t
  have hdcx : ∀ᵐ x ∂μ.restrict O,
      ContinuousOn (fun t => scalarCurvature (h (timeClamp S hS.le t)) x) (Icc 0 S) := by
    apply ae_of_all
    intro x
    exact (hRc.comp_continuous (continuous_const.prodMk (continuous_timeClamp S hS.le))
      (fun t => ⟨mem_univ x, timeClamp_mem S hS.le t⟩)).continuousOn
  have hC1 := finiteLpCurve_contDiffOn_one (μ.restrict O)
    (fun t x => ρ x (timeClamp S hS.le t))
    (fun t x => scalarCurvature (h (timeClamp S hS.le t)) x) hf hd hS C hC hder hdb hdcx
  have hzero : (hf 0).toLp (fun x => ρ x (timeClamp S hS.le 0)) = 0 := by
    apply Lp.ext
    filter_upwards [(hf 0).coeFn_toLp,
      Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ.restrict O)] with x hx hz
    rw [hx, timeClamp_eq_of_mem S hS.le ⟨le_rfl, hS.le⟩, rho_initial o h U P ρ hloc, hz]
    rfl
  refine ⟨hf, hd, hfc, hdc, hC1, hzero, ?_⟩
  exact finiteLpCurve_hasDerivWithinAt (μ.restrict O)
    (fun t x => ρ x (timeClamp S hS.le t))
    (fun t x => scalarCurvature (h (timeClamp S hS.le t)) x) hf hd hS C hC hder hdb

end Yau.F04Proof

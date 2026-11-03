import Yau.Proofs.F04VariationalSmoothComparison
import Yau.Proofs.F04IntrinsicFormBinding
import Yau.Proofs.F04FlowRhoLp
import Yau.Proofs.F04CompactDifferentialProfiles
import Yau.Proofs.F04FlowSourceLp

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.F04Proof

open Yau.Blueprint Yau.Proofs.F03Aux Yau.MassTargetStatements Yau.HeatConcreteBindings

variable {n : ℕ}

local instance (X : KahlerManifold n) (μ : Measure (Pt X))
    (hμ : IsRiemannianVolume X.metric.form μ) (O : Set (Pt X)) :
    CompleteSpace (DirichletEnergy X.metric μ hμ O) := dirichletEnergy_completeSpace X.metric μ hμ O

/-- The supplied flow's own rho dominates every actual zero-initial supported
 weak solution whose source is bounded above by its actual source F. All
 comparison profiles, larger-domain forms and compact matches are constructed. -/
theorem flow_variationalSolution_le_rho
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O K : Set (Pt X)) (hO : IsOpen O) (hK : IsCompact K) (hOK : O ⊆ K)
    {T C α shift : ℝ} (hT : 0 < T)
    (B : ℝ → DirichletEnergy X.metric μ hμ O →L[ℝ]
      EnergyDual (DirichletEnergy X.metric μ hμ O))
    (hForm : IntrinsicFormBinding X.metric.form μ O h T C α shift
      (dirichletL2 X.metric μ hμ O) (energyRepresentative X.metric μ hμ O) B)
    (f : ℝ → FixedPivot μ O) (u : ℝ → DirichletEnergy X.metric μ hμ O)
    (w : ℝ → EnergyDual (DirichletEnergy X.metric μ hμ O)) (a : ℝ → FixedPivot μ O)
    (hSol : VariationalSolution μ O T (dirichletL2 X.metric μ hμ O) B f u w a)
    (hSrc : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ∀ᵐ x ∂μ.restrict O, f t x ≤ source X h x t) :
    ∀ t ∈ Icc 0 T, ∀ᵐ x ∂μ.restrict O, a t x ≤ ρ x t := by
  let : LocallyCompactSpace (Pt X) := Yau.LeafProofs.L12Aux.manifold_locallyCompact X.manifold
  have hOC : IsCompact (closure O) := hK.of_isClosed_subset isClosed_closure (closure_minimal hOK hK.isClosed)
  obtain ⟨W, hW, hOW, hWC⟩ := exists_isOpen_superset_and_isCompact_closure hOC
  have hOW' : O ⊆ W := subset_closure.trans hOW
  obtain ⟨ψ, N, hψ, hcψ, hψW, _hN, hON, _hNW, hψOne, hψRange⟩ :=
    exists_supported_smooth_cutoff (closure O) W hOC hW hOW
  obtain ⟨A, D, shiftW, hFormW⟩ := flow_intrinsic_form_binding X o h U P ρ hloc μ hμ W (closure W)
    hW hWC subset_closure hT
  obtain ⟨hf, hd, hRhoC, _hRC, hRhoC1, _hRho0, hDer⟩ :=
    flow_rho_L2_profiles X o h U P ρ hloc μ hμ O K hO.measurableSet hK hOK hT
  let r : ℝ → Pt X → ℝ := fun t x => ρ x (timeClamp T hT.le t)
  have hρ : SmoothSpaceTime ρ (Icc 0 T) := fun c => (hloc.2.2.2.1 c).mono
    (prod_mono (Subset.refl _) (fun _ ht => ht.1))
  have hr (t : ℝ) : SmoothFn (r t) := fun c => (hρ c).comp
    (contDiffOn_id.prodMk contDiffOn_const) (fun _ hz => ⟨hz, timeClamp_mem T hT.le t⟩)
  have hr0 (t : ℝ) (x : Pt X) : 0 ≤ r t x :=
    rho_nonneg o h U P ρ hloc x _ (timeClamp_mem T hT.le t).1
  let hr2 : ∀ t, ScalarL2 (μ.restrict O) (r t) := fun t => (scalarL2_iff_memLp _ _).mpr (hf t)
  obtain ⟨hdr2, hRD⟩ := compact_scalar_differential_profile_L2 X.metric μ hμ O K
    hO.measurableSet hK hOK hT ρ hρ
  let b : ℝ → FixedPivot μ O := fun t => (hf t).toLp (fun x => ρ x (timeClamp T hT.le t))
  have hbval (t : ℝ) (_ht : t ∈ Icc 0 T) : b t = scalarToLp (hr2 t) := rfl
  have hRH : Continuous (fun t => scalarToLp (hr2 t)) := hRhoC
  let q : ℝ → dirichletCore X.metric μ hμ W := fun t =>
    ⟨⟨(fun x => ψ x * r t x), (fun c => (hψ c).mul (hr t c)), hcψ.mul_right⟩,
      tsupport_mul_subset_left.trans hψW⟩
  have hq0 (t : ℝ) (x : Pt X) (_hx : x ∈ W) : 0 ≤ (q t).val x :=
    mul_nonneg (hψRange x).1 (hr0 t x)
  have hqr (t : ℝ) (x : Pt X) (hx : x ∈ O) : (q t).val x = r t x := by
    change ψ x * r t x = r t x
    rw [hψOne x (hON (subset_closure hx)), one_mul]
  have hh (t : ℝ) (ht : t ∈ Icc 0 T) : MetricSmooth (h t) :=
    metricFamilySmooth_slice h (Ici 0) hloc.1.2.1 t ht.1
  have hSup : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ∀ᵐ x ∂μ.restrict O,
      f t x ≤ derivWithin b (Icc 0 T) t x - laplacian (h t) (r t) x := by
    filter_upwards [hSrc, ae_restrict_mem measurableSet_Ioo] with t hst ht
    have htC : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
    have hDb : derivWithin b (Icc 0 T) t =
        (hd t).toLp (fun x => scalarCurvature (h (timeClamp T hT.le t)) x) :=
      (hDer t htC).derivWithin (uniqueDiffOn_Icc hT t htC)
    have hrEq : r t = fun x => ρ x t := by
      funext x
      exact congrArg (ρ x) (timeClamp_eq_of_mem T hT.le htC)
    filter_upwards [hst, (hd t).coeFn_toLp] with x hfx hDx
    rw [hDb, hDx, timeClamp_eq_of_mem T hT.le htC, hrEq]
    have he := rho_source_equation o h U P ρ hloc T hT x t htC
    unfold heatOp at he
    rw [rho_derivWithin_Icc o h U P ρ hloc T hT x t htC] at he
    rw [← he] at hfx
    exact hfx
  have hc := variationalSolution_smooth_comparison X.metric X.kahler_metric μ hμ hO hW hOW' h hT
    B A hForm hFormW hh r hr (fun t x _ => hr0 t x) hr2 hdr2 hRH hRD
    b hRhoC1 hbval q hq0 hqr f u w a hSol hSup
  intro t ht
  filter_upwards [hc t ht, (hf t).coeFn_toLp] with x hax hbx
  change a t x ≤ (hf t).toLp (fun y => ρ y (timeClamp T hT.le t)) x at hax
  rw [hbx, timeClamp_eq_of_mem T hT.le ht] at hax
  exact hax

end Yau.F04Proof

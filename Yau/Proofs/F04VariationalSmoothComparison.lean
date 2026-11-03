import Yau.Proofs.F04ShiftLocalFormIdentity
import Yau.Proofs.F04PhysicalWeakMaximum
import Yau.Proofs.F04VariationalTime
import Yau.Proofs.F04LpOrderPairing

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.HeatConcreteBindings Yau.MassTargetStatements Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

local instance (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    CompleteSpace (DirichletEnergy g μ hμ O) := dirichletEnergy_completeSpace g μ hμ O

/-- Comparison of the original variational trace with a genuine smooth
 supersolution. The shifted form identity and its compact matching profile
 are constructed in the original supported spaces. -/
theorem variationalSolution_smooth_comparison
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {O W : Set M.Carrier}
    (hO : IsOpen O) (hW : IsOpen W) (hOW : O ⊆ W)
    (h : ℝ → HermitianField M) {T C α shift D β shiftW : ℝ} (hT : 0 < T)
    (B : ℝ → DirichletEnergy g μ hμ O →L[ℝ] EnergyDual (DirichletEnergy g μ hμ O))
    (A : ℝ → DirichletEnergy g μ hμ W →L[ℝ] EnergyDual (DirichletEnergy g μ hμ W))
    (hForm : IntrinsicFormBinding g.form μ O h T C α shift
      (dirichletL2 g μ hμ O) (energyRepresentative g μ hμ O) B)
    (hFormW : IntrinsicFormBinding g.form μ W h T D β shiftW
      (dirichletL2 g μ hμ W) (energyRepresentative g μ hμ W) A)
    (hh : ∀ t ∈ Icc 0 T, MetricSmooth (h t))
    (r : ℝ → M.Carrier → ℝ) (hr : ∀ t, SmoothFn (r t)) (hr0 : ∀ t x, x ∈ O → 0 ≤ r t x)
    (hr2 : ∀ t, ScalarL2 (μ.restrict O) (r t))
    (hdr2 : ∀ t, L2RealForm g.form (μ.restrict O) (scalarExterior (r t)))
    (hRH : Continuous (fun t => scalarToLp (hr2 t)))
    (hRD : Continuous (fun t => realizeL2Form g (μ.restrict O)
      (L2FormSpace.ofSection (scalarExterior (r t)) (hdr2 t))))
    (b : ℝ → FixedPivot μ O) (hb : ContDiffOn ℝ 1 b (Icc 0 T))
    (hbval : ∀ t ∈ Icc 0 T, b t = scalarToLp (hr2 t))
    (q : ℝ → dirichletCore g μ hμ W) (hq0 : ∀ t x, x ∈ W → 0 ≤ (q t).val x)
    (hqr : ∀ t x, x ∈ O → (q t).val x = r t x)
    (f : ℝ → FixedPivot μ O) (U : ℝ → DirichletEnergy g μ hμ O)
    (R : ℝ → EnergyDual (DirichletEnergy g μ hμ O)) (a : ℝ → FixedPivot μ O)
    (hSol : VariationalSolution μ O T (dirichletL2 g μ hμ O) B f U R a)
    (hSup : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ∀ᵐ x ∂μ.restrict O,
      f t x ≤ derivWithin b (Icc 0 T) t x - laplacian (h t) (r t) x) :
    ∀ t ∈ Icc 0 T, ∀ᵐ x ∂μ.restrict O, a t x ≤ b t x := by
  let j := dirichletL2 g μ hμ O
  let I := dirichletInclusion g μ hμ hOW
  have hw := variationalSolution_weak_time μ O hT j B f U R a hSol
  rcases hSol with ⟨hU, hR, ha, ha0, hae, _hscalar, hEq⟩
  have hInit : ∀ᵐ x ∂μ.restrict O, a 0 x ≤ b 0 x := by
    rw [ha0, hbval 0 ⟨le_rfl, hT.le⟩]
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ.restrict O),
      scalarToLp_coe (hr2 0), ae_restrict_mem hO.measurableSet] with x hz hrx hx
    rw [hz, Pi.zero_apply, hrx]
    exact hr0 0 x hx
  have hBound : ∀ᵐ t ∂volume.restrict (Ioo 0 T),
      let w := dirichletShiftPosPart g μ hμ O hO (r t) (hr t) (hr0 t) (hr2 t) (hdr2 t) (U t)
      R t w - inner ℝ (derivWithin b (Icc 0 T) t) (j w) ≤ shiftW * ‖Lp.posPart (a t - b t)‖ ^ 2 := by
    filter_upwards [hEq, hae, hSup, ae_restrict_mem measurableSet_Ioo] with t het hat hst ht
    have htC : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
    let w := dirichletShiftPosPart g μ hμ O hO (r t) (hr t) (hr0 t) (hr2 t) (hdr2 t) (U t)
    obtain ⟨hL, hid⟩ := localCoreForm_shift_identity_local g hK μ hμ hO hW hOW (h t) (hh t htC)
      (B t) (A t)
      (intrinsicForm_core_formula g hK μ hμ O hO h T C α shift B hForm t htC)
      (intrinsicForm_core_formula g hK μ hμ W hW h T D β shiftW A hFormW t htC)
      (r t) (hr t) (hr0 t) (hr2 t) (hdr2 t) (q t) (hq0 t) (hqr t) (U t)
    change B t (U t) w + inner ℝ (scalarToLp hL) (j w) = A t (I w) (I w) at hid
    have hJw : j w = Lp.posPart (a t - b t) := by
      change dirichletL2 g μ hμ O (dirichletShiftPosPart g μ hμ O hO (r t) (hr t) (hr0 t) (hr2 t) (hdr2 t) (U t)) = _
      rw [(dirichletShiftPosPart_spec g μ hμ O hO (r t) (hr t) (hr0 t) (hr2 t) (hdr2 t) (U t)).1,
        ← hat, ← hbval t htC]
    have hW0 : ∀ᵐ x ∂μ.restrict O, 0 ≤ j w x := by
      rw [hJw]
      filter_upwards [Lp.coeFn_posPart (a t - b t)] with x hx
      rw [hx]
      exact le_max_right _ _
    have hOrder : ∀ᵐ x ∂μ.restrict O,
        f t x ≤ (derivWithin b (Icc 0 T) t - scalarToLp hL) x := by
      filter_upwards [hst, Lp.coeFn_sub (derivWithin b (Icc 0 T) t) (scalarToLp hL), scalarToLp_coe hL]
        with x hfx hsx hLx
      rw [hsx, Pi.sub_apply, hLx]
      exact hfx
    have hInner := lp_inner_sub_nonpos_of_ae (μ.restrict O) (f t)
      (derivWithin b (Icc 0 T) t - scalarToLp hL) (j w) hOrder hW0
    rw [inner_sub_left, inner_sub_left] at hInner
    have hG := (hFormW.2.2.2.2 t htC).2.1 (I w)
    rw [dirichletInclusion_L2_norm g μ hμ hO.measurableSet hW.measurableSet hOW w, hJw] at hG
    have hβ : 0 ≤ β * ‖I w‖ ^ 2 := mul_nonneg hFormW.2.1.le (sq_nonneg _)
    have he := het w
    change R t w - inner ℝ (derivWithin b (Icc 0 T) t) (j w) ≤ shiftW * ‖Lp.posPart (a t - b t)‖ ^ 2
    linarith only [he, hid, hInner, hG, hβ]
  exact dirichlet_shift_posPart_physical_weak_maximum g hK μ hμ O hO r hr hr0 hr2 hdr2 hRH hRD
    hT b hb hbval hU hR hw a ha (hae.mono (fun _ he => he.symm))
    shiftW hFormW.2.2.1 hInit hBound

end Yau.F04Proof

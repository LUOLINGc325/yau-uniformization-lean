import Yau.Proofs.F04ShiftJointContinuity
import Yau.Proofs.F04PositiveEnergyHilbert
import Yau.Proofs.F04ClosedTimeFTC
import Yau.LeafProofs.L16LionsTimeTrace

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace
noncomputable section
namespace Yau.F04Proof
open Yau.Proofs.F03Aux Yau.LeafProofs.L03 Yau.HeatConcreteBindings
  Yau.LeafProofs.L16HilbertTimeRegularization Yau.LeafProofs.L16LionsTimeTrace
variable {n : ℕ} {M : ComplexManifold n}

theorem dirichlet_hasDerivAt_pointShiftedPositiveEnergy
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (r : ℝ → M.Carrier → ℝ) (hr : ∀ t, SmoothFn (r t)) (hr0 : ∀ t x, x ∈ O → 0 ≤ r t x)
    (hr2 : ∀ t, ScalarL2 (μ.restrict O) (r t))
    (hdr2 : ∀ t, L2RealForm g.form (μ.restrict O) (scalarExterior (r t)))
    (b : ℝ → Lp ℝ 2 (μ.restrict O))
    {z : ℝ → DirichletEnergy g μ hμ O} (hz : ContDiff ℝ 1 z)
    {Q : ℝ → StrongDual ℝ (DirichletEnergy g μ hμ O)} (t : ℝ)
    (db : Lp ℝ 2 (μ.restrict O)) (hdb : HasDerivAt b db t)
    (hbval : b t = scalarToLp (hr2 t))
    (hQ : hilbertEmbedding (dirichletL2 g μ hμ O) (deriv z t) = Q t) :
    HasDerivAt (fun q => positiveEnergy (dirichletL2 g μ hμ O (z q) - b q))
      (Q t (dirichletShiftPosPart g μ hμ O hO (r t) (hr t) (hr0 t) (hr2 t) (hdr2 t) (z t)) -
        inner ℝ (db) (dirichletL2 g μ hμ O
          (dirichletShiftPosPart g μ hμ O hO (r t) (hr t) (hr0 t) (hr2 t) (hdr2 t) (z t)))) t := by
  let J := dirichletL2 g μ hμ O
  let w := dirichletShiftPosPart g μ hμ O hO (r t) (hr t) (hr0 t) (hr2 t) (hdr2 t) (z t)
  have hJP : J w = Lp.posPart (J (z t) - b t) := by
    rw [hbval]
    exact (dirichletShiftPosPart_spec g μ hμ O hO (r t) (hr t) (hr0 t) (hr2 t) (hdr2 t) (z t)).1
  have hd : HasDerivAt z (deriv z t) t :=
    (hz.differentiable (by simp)).differentiableAt.hasDerivAt
  have hEnergy := (positiveEnergy_hasFDerivAt (J (z t) - b t)).comp_hasDerivAt t
    ((J.hasFDerivAt.comp_hasDerivAt t hd).sub hdb)
  have hQw : Q t w = inner ℝ (J (deriv z t)) (J w) := by
    rw [← hQ, hilbertEmbedding_apply]
  have he : inner ℝ (Lp.posPart (J (z t) - b t)) (J (deriv z t) - db) =
      Q t w - inner ℝ (db) (J w) := by
    rw [← hJP, inner_sub_right, real_inner_comm (J (deriv z t)) (J w),
      real_inner_comm (db) (J w), ← hQw]
  change HasDerivAt (fun q => positiveEnergy (J (z q) - b q))
    (inner ℝ (Lp.posPart (J (z t) - b t)) (J (deriv z t) - db)) t at hEnergy
  rw [he] at hEnergy
  exact hEnergy

theorem smooth_physical_shifted_positive_energy_increment
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (r : ℝ → M.Carrier → ℝ) (hr : ∀ t, SmoothFn (r t)) (hr0 : ∀ t x, x ∈ O → 0 ≤ r t x)
    (hr2 : ∀ t, ScalarL2 (μ.restrict O) (r t))
    (hdr2 : ∀ t, L2RealForm g.form (μ.restrict O) (scalarExterior (r t)))
    (hRH : Continuous (fun t => scalarToLp (hr2 t)))
    (hRD : Continuous (fun t => realizeL2Form g (μ.restrict O)
      (L2FormSpace.ofSection (scalarExterior (r t)) (hdr2 t))))
    {T : ℝ} (hT : 0 < T) (b : ℝ → Lp ℝ 2 (μ.restrict O))
    (hb : ContDiffOn ℝ 1 b (Icc 0 T)) (hbval : ∀ t ∈ Icc 0 T, b t = scalarToLp (hr2 t))
    {z : ℝ → DirichletEnergy g μ hμ O} (hz : ContDiff ℝ 1 z)
    {Q : ℝ → StrongDual ℝ (DirichletEnergy g μ hμ O)}
    (hQc : ContinuousOn Q (Icc 0 T))
    (hd : ∀ t ∈ Icc 0 T, hilbertEmbedding (dirichletL2 g μ hμ O) (deriv z t) = Q t)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    ‖Lp.posPart (dirichletL2 g μ hμ O (z t) - b t)‖ ^ 2 -
      ‖Lp.posPart (dirichletL2 g μ hμ O (z s) - b s)‖ ^ 2 =
      2 * ∫ q in s..t,
        Q q (dirichletShiftPosPart g μ hμ O hO (r q) (hr q) (hr0 q) (hr2 q) (hdr2 q) (z q)) -
          inner ℝ (derivWithin b (Icc 0 T) q) (dirichletL2 g μ hμ O
            (dirichletShiftPosPart g μ hμ O hO (r q) (hr q) (hr0 q) (hr2 q) (hdr2 q) (z q))) := by
  let J := dirichletL2 g μ hμ O
  let W := fun q => dirichletShiftPosPart g μ hμ O hO (r q) (hr q) (hr0 q) (hr2 q) (hdr2 q) (z q)
  let Φ : ℝ × DirichletEnergy g μ hμ O → DirichletEnergy g μ hμ O := fun p =>
    dirichletShiftPosPart g μ hμ O hO (r p.1) (hr p.1) (hr0 p.1) (hr2 p.1) (hdr2 p.1) p.2
  have hΦ : Continuous Φ :=
    continuous_dirichletShiftPosPart_family g hK μ hμ O hO r hr hr0 hr2 hdr2 hRH hRD
  have hW : Continuous W := by
    simpa only [Function.comp_def, Φ, W, id_eq] using hΦ.comp (continuous_id.prodMk hz.continuous)
  have hdb := hb.continuousOn_derivWithin (uniqueDiffOn_Icc hT) le_rfl
  have hS : ContinuousOn (fun q => Q q - hilbertPivot J (derivWithin b (Icc 0 T) q)) (Icc 0 T) :=
    hQc.sub ((hilbertPivot J).continuous.comp_continuousOn hdb)
  have hc : ContinuousOn (fun q => Q q (W q) -
      inner ℝ (derivWithin b (Icc 0 T) q) (J (W q))) (Icc 0 T) := by
    change ContinuousOn (fun q => (Q q - hilbertPivot J (derivWithin b (Icc 0 T) q)) (W q)) (Icc 0 T)
    exact hS.clm_apply hW.continuousOn
  have hy : ContinuousOn (fun q => positiveEnergy (J (z q) - b q)) (Icc 0 T) :=
    positiveEnergy_contDiff.continuous.comp_continuousOn
      ((J.continuous.comp_continuousOn hz.continuous.continuousOn).sub hb.continuousOn)
  have hder : ∀ q ∈ Ioo 0 T, HasDerivAt (fun q => positiveEnergy (J (z q) - b q))
      (Q q (W q) - inner ℝ (derivWithin b (Icc 0 T) q) (J (W q))) q := by
    intro q hq
    have hqcc : q ∈ Icc 0 T := ⟨hq.1.le, hq.2.le⟩
    have hdbq := ((hb.differentiableOn (by norm_num)) q hqcc).hasDerivWithinAt.hasDerivAt
      (Icc_mem_nhds hq.1 hq.2)
    exact dirichlet_hasDerivAt_pointShiftedPositiveEnergy g μ hμ O hO r hr hr0 hr2 hdr2
      b hz q (derivWithin b (Icc 0 T) q) hdbq (hbval q hqcc) (hd q hqcc)
  have he := closed_time_FTC hy hc.integrableOn_Icc hder hs ht
  dsimp only [positiveEnergy] at he
  change ‖Lp.posPart (J (z t) - b t)‖ ^ 2 - ‖Lp.posPart (J (z s) - b s)‖ ^ 2 =
    2 * ∫ q in s..t, Q q (W q) - inner ℝ (derivWithin b (Icc 0 T) q) (J (W q))
  linarith

end Yau.F04Proof

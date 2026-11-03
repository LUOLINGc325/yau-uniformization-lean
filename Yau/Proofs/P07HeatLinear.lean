import Yau.Proofs.P06ContinuousHeatHilbert
import Yau.LeafProofs.L19HeatClassicalCore

/-! Pointwise linearity of the actual classical L² heat representative.
The continuous representative is identified through the original volume. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.NodeProofs.P07Aux
open Yau Yau.Blueprint Yau.LeafProofs.L19Aux Yau.LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem scalarClassicalHeat_continuous (hn : 0 < n) (g : SmoothMetric M)
    (hk : IsKahler g) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (f : Lp ℝ 2 μ) {t : ℝ} (ht : 0 < t) :
    Continuous (fun x => scalarClassicalHeat hn g hk μ hμ f x t) :=
  continuous_of_smoothFn (smoothSpaceTime_slice (scalarClassicalHeat_smooth hn g hk μ hμ f) ht)

theorem scalarClassicalHeat_add (hn : 0 < n) (g : SmoothMetric M)
    (hk : IsKahler g) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (f q : Lp ℝ 2 μ) (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    scalarClassicalHeat hn g hk μ hμ (f + q) x t =
      scalarClassicalHeat hn g hk μ hμ f x t + scalarClassicalHeat hn g hk μ hμ q x t := by
  letI : μ.IsOpenPosMeasure := riemannianVolume_isOpenPosMeasure g μ hμ
  have hae : (fun z => scalarClassicalHeat hn g hk μ hμ (f + q) z t) =ᵐ[μ]
      (fun z => scalarClassicalHeat hn g hk μ hμ f z t +
        scalarClassicalHeat hn g hk μ hμ q z t) := by
    have he := scalarClassicalHeat_ae hn g hk μ hμ (f + q) ht
    rw [map_add] at he
    filter_upwards [he, Lp.coeFn_add (scalarHeatFamily g μ hμ t f) (scalarHeatFamily g μ hμ t q),
      scalarClassicalHeat_ae hn g hk μ hμ f ht, scalarClassicalHeat_ae hn g hk μ hμ q ht]
      with z hz ha hf hq
    simpa only [ha, Pi.add_apply, ← hf, ← hq] using hz
  exact congrFun (MeasureTheory.Measure.eq_of_ae_eq hae
    (scalarClassicalHeat_continuous hn g hk μ hμ (f + q) ht)
    ((scalarClassicalHeat_continuous hn g hk μ hμ f ht).add
      (scalarClassicalHeat_continuous hn g hk μ hμ q ht))) x

theorem scalarClassicalHeat_smul (hn : 0 < n) (g : SmoothMetric M)
    (hk : IsKahler g) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (c : ℝ) (f : Lp ℝ 2 μ) (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    scalarClassicalHeat hn g hk μ hμ (c • f) x t =
      c * scalarClassicalHeat hn g hk μ hμ f x t := by
  letI : μ.IsOpenPosMeasure := riemannianVolume_isOpenPosMeasure g μ hμ
  have hae : (fun z => scalarClassicalHeat hn g hk μ hμ (c • f) z t) =ᵐ[μ]
      (fun z => c * scalarClassicalHeat hn g hk μ hμ f z t) := by
    have he := scalarClassicalHeat_ae hn g hk μ hμ (c • f) ht
    rw [map_smul] at he
    filter_upwards [he, Lp.coeFn_smul c (scalarHeatFamily g μ hμ t f),
      scalarClassicalHeat_ae hn g hk μ hμ f ht] with z hz ha hf
    simpa only [ha, Pi.smul_apply, smul_eq_mul, ← hf] using hz
  exact congrFun (MeasureTheory.Measure.eq_of_ae_eq hae
    (scalarClassicalHeat_continuous hn g hk μ hμ (c • f) ht)
    ((scalarClassicalHeat_continuous hn g hk μ hμ f ht).const_mul c)) x

theorem scalarClassicalHeat_neg (hn : 0 < n) (g : SmoothMetric M)
    (hk : IsKahler g) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (f : Lp ℝ 2 μ) (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    scalarClassicalHeat hn g hk μ hμ (-f) x t =
      -scalarClassicalHeat hn g hk μ hμ f x t := by
  simpa only [neg_one_smul, neg_one_mul] using
    scalarClassicalHeat_smul hn g hk μ hμ (-1) f x ht

/-- Every original continuous-initial solution with exterior value one has
an actual complementary L² datum and its pointwise classical realization. -/
theorem continuousInitialHeat_complementary_representation (X : KahlerManifold n)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (f : Pt X → ℝ) (hc : Continuous (fun x => f x - 1))
    (hcomp : HasCompactSupport (fun x => f x - 1))
    (U : ℝ → Pt X → ℝ) (hU : IsContinuousInitialScalarHeat X.metric.form f U) :
    ∃ q : Lp ℝ 2 μ, (q =ᵐ[μ] (fun x => 1 - f x)) ∧
      ∀ t, 0 < t → ∀ x,
        U t x = 1 - scalarClassicalHeat
          (Yau.LeafProofs.L12Aux.complexDimension_pos X.manifold) X.metric X.kahler_metric μ hμ q x t := by
  obtain ⟨hf, hrep⟩ := P06Aux.continuousInitialHeat_normalized_representation X μ hμ f 1 hc hcomp U hU
  let fL := hf.toLp (fun x => f x - 1)
  let q : Lp ℝ 2 μ := -fL
  have hq : q =ᵐ[μ] (fun x => 1 - f x) := by
    filter_upwards [Lp.coeFn_neg fL, hf.coeFn_toLp] with x hx hfx
    simp only [q, hx, Pi.neg_apply, fL, hfx]
    ring
  refine ⟨q, hq, ?_⟩
  intro t ht
  let hn := Yau.LeafProofs.L12Aux.complexDimension_pos X.manifold
  letI : μ.IsOpenPosMeasure := riemannianVolume_isOpenPosMeasure X.metric μ hμ
  have he : (fun x => U t x - 1) = (fun x => scalarClassicalHeat hn X.metric X.kahler_metric μ hμ fL x t) :=
    MeasureTheory.Measure.eq_of_ae_eq
      ((hrep t ht).trans (scalarClassicalHeat_ae hn X.metric X.kahler_metric μ hμ fL ht).symm)
      ((continuous_of_smoothFn (smoothSpaceTime_slice hU.2.1 ht)).sub continuous_const)
      (scalarClassicalHeat_continuous hn X.metric X.kahler_metric μ hμ fL ht)
  intro x
  have hx := congrFun he x
  rw [show q = -fL from rfl, scalarClassicalHeat_neg hn X.metric X.kahler_metric μ hμ fL x ht]
  linarith

end Yau.NodeProofs.P07Aux

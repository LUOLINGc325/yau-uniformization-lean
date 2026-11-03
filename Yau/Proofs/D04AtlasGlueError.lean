import Yau.Proofs.D04AtlasGlueVolumeCompare
import Yau.Proofs.D04Distance

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace Yau.Proofs.D04AtlasGlueAux

open Yau Yau.Blueprint

variable {α : Type*} [MeasurableSpace α]

theorem measurable_erealDist {p q : α → EReal} (hp : Measurable p) (hq : Measurable q) :
    Measurable (fun x => erealDist (p x) (q x)) := by
  classical
  unfold erealDist
  apply Measurable.ite (measurableSet_eq_fun hp hq) measurable_const
  have hset : MeasurableSet {x | p x = ⊥ ∨ p x = ⊤ ∨ q x = ⊥ ∨ q x = ⊤} := by
    exact (hp (measurableSet_singleton ⊥)).union
      ((hp (measurableSet_singleton ⊤)).union
        ((hq (measurableSet_singleton ⊥)).union (hq (measurableSet_singleton ⊤))))
  apply Measurable.ite hset measurable_const
  exact (hp.ereal_toReal.sub hq.ereal_toReal).abs.ennreal_ofReal

theorem aemeasurable_erealDist {μ : Measure α} {p q : α → EReal}
    (hp : AEMeasurable p μ) (hq : AEMeasurable q μ) :
    AEMeasurable (fun x => erealDist (p x) (q x)) μ := by
  apply (measurable_erealDist hp.measurable_mk hq.measurable_mk).aemeasurable.congr
  filter_upwards [hp.ae_eq_mk, hq.ae_eq_mk] with x hpx hqx
  exact congrArg₂ erealDist hpx.symm hqx.symm

/-- Original EReal-error convergence identifies measurable limits for the
same sequence, including all infinite values. Only its actual measurable
tail is used. -/
theorem limits_unique_of_erealDist {μ : Measure α}
    {us : ℕ → α → EReal} {p q : α → EReal}
    (hus : ∀ᶠ j in atTop, AEMeasurable (us j) μ)
    (hp : AEMeasurable p μ) (hq : AEMeasurable q μ)
    (htp : Tendsto (fun j => ∫⁻ x, erealDist (us j x) (p x) ∂μ) atTop (𝓝 0))
    (htq : Tendsto (fun j => ∫⁻ x, erealDist (us j x) (q x) ∂μ) atTop (𝓝 0)) :
    p =ᵐ[μ] q := by
  have hbound : ∀ᶠ j in atTop, (∫⁻ x, erealDist (p x) (q x) ∂μ) ≤
      (∫⁻ x, erealDist (us j x) (p x) ∂μ) +
        (∫⁻ x, erealDist (us j x) (q x) ∂μ) := by
    filter_upwards [hus] with j hj
    calc
      _ ≤ ∫⁻ x, erealDist (p x) (us j x) + erealDist (us j x) (q x) ∂μ :=
        lintegral_mono (fun x => D04Aux.erealDist_triangle _ _ _)
      _ = _ := by
        rw [lintegral_add_left' (aemeasurable_erealDist hp hj)]
        simp_rw [D04Aux.erealDist_comm (p _) (us j _)]
  have hzero : (∫⁻ x, erealDist (p x) (q x) ∂μ) = 0 := by
    apply le_antisymm _ bot_le
    exact ge_of_tendsto (by simpa using htp.add htq) hbound
  have hae := (lintegral_eq_zero_iff' (aemeasurable_erealDist hp hq)).mp hzero
  exact hae.mono (fun x hx => D04Aux.erealDist_eq_zero_iff.mp hx)

theorem one_le_erealDist_of_le_sub_one {a b : EReal}
    (hbtop : b ≠ ⊤) (hbbot : b ≠ ⊥)
    (hab : a ≤ ((b.toReal - 1 : ℝ) : EReal)) : 1 ≤ erealDist a b := by
  by_cases haeq : a = b
  · subst a
    rw [← EReal.coe_toReal hbtop hbbot] at hab
    have h : b.toReal ≤ b.toReal - 1 := EReal.coe_le_coe_iff.mp hab
    linarith
  by_cases habot : a = ⊥
  · simp [erealDist, habot, hbbot.symm]
  by_cases hatop : a = ⊤
  · simp [erealDist, hatop, hbtop.symm]
  have habreal : a.toReal ≤ b.toReal - 1 := by
    apply EReal.coe_le_coe_iff.mp
    rw [EReal.coe_toReal hatop habot]
    exact hab
  rw [erealDist, ite_eq_right haeq, ite_eq_right (by tauto)]
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  have := neg_le_abs (a.toReal - b.toReal)
  linarith

/-- Positive mass excludes uniform upper collapse when the original
EReal errors converge to zero and the limit is finite a.e. This is also the
mixed-chart branch exclusion used in the atlas argument. -/
theorem not_collapse_on_positive_mass
    {μ : Measure α} {K : Set α} (hK : MeasurableSet K) (hKpos : 0 < μ K)
    {us : ℕ → α → EReal} {v : α → EReal}
    (hfinite : ∀ᵐ x ∂μ.restrict K, v x ≠ ⊥ ∧ v x ≠ ⊤)
    (hmeas : ∀ᶠ j in atTop,
      AEMeasurable (fun x => erealDist (us j x) (v x)) (μ.restrict K))
    (hconv : Tendsto (fun j => ∫⁻ x in K, erealDist (us j x) (v x) ∂μ) atTop (𝓝 0)) :
    ¬ (∀ A : ℝ, ∃ N : ℕ, ∀ j, N ≤ j → ∀ x ∈ K, us j x ≤ ((-A : ℝ) : EReal)) := by
  intro hcollapse
  obtain ⟨N, hN⟩ := eventually_atTop.mp hmeas
  let f : ℕ → α → ℝ≥0∞ := fun j x => erealDist (us (j + N) x) (v x)
  have hliminf : ∀ᵐ x ∂μ.restrict K, 1 ≤ liminf (fun j => f j x) atTop := by
    filter_upwards [hfinite, ae_restrict_mem hK] with x hx hxK
    obtain ⟨J, hJ⟩ := hcollapse (1 - (v x).toReal)
    apply le_liminf_of_le (by isBoundedDefault)
    filter_upwards [eventually_ge_atTop J] with j hj
    apply one_le_erealDist_of_le_sub_one hx.2 hx.1
    have heq : -(1 - (v x).toReal) = (v x).toReal - 1 := by ring
    simpa only [heq] using hJ (j + N) (by omega) x hxK
  have hlower : μ K ≤ ∫⁻ x in K, liminf (fun j => f j x) atTop ∂μ := by
    simpa only [lintegral_const, one_mul, Measure.restrict_apply_univ] using
      (lintegral_mono_ae hliminf)
  have hfatou := lintegral_liminf_le' (μ := μ.restrict K) (u := atTop) (f := f)
    (fun j => hN (j + N) (by omega))
  have ht : Tendsto (fun j => ∫⁻ x in K, f j x ∂μ) atTop (𝓝 0) :=
    hconv.comp (tendsto_add_atTop_nat N)
  have hzero : μ K ≤ 0 := by
    calc
      μ K ≤ ∫⁻ x in K, liminf (fun j => f j x) atTop ∂μ := hlower
      _ ≤ liminf (fun j => ∫⁻ x in K, f j x ∂μ) atTop := hfatou
      _ = 0 := ht.liminf_eq
  exact (not_le_of_gt hKpos) hzero

end Yau.Proofs.D04AtlasGlueAux

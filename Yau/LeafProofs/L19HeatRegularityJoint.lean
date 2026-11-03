import Yau.LeafProofs.L19HeatRegularityChartTest
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-! Joint representatives of actual L²-valued time paths, constructed
from finite simple paths and actual product L² limits. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}

/-- A finite simple path of actual L² classes has a genuine joint
representative obtained from its finitely many actual representatives. -/
def scalarSimpleL2Joint (s : SimpleFunc β (Lp ℝ 2 μ)) (p : α × β) : ℝ := s p.2 p.1

theorem scalarSimpleL2Joint_measurable (s : SimpleFunc β (Lp ℝ 2 μ)) :
    Measurable (scalarSimpleL2Joint s) :=
  (s.comp Prod.snd measurable_snd).measurable_bind (fun h p => h p.1)
    (fun h => (Lp.stronglyMeasurable h).measurable.comp measurable_fst)

theorem scalarSimpleL2Joint_memLp [IsFiniteMeasure ν] (s : SimpleFunc β (Lp ℝ 2 μ)) :
    MemLp (scalarSimpleL2Joint s) 2 (μ.prod ν) := by
  classical
  have hsum : MemLp (fun p : α × β => ∑ h ∈ s.range, ‖h p.1‖) 2 (μ.prod ν) :=
    memLp_finsetSum s.range (fun h _ => ((Lp.memLp h).comp_fst ν).norm)
  apply hsum.mono' (scalarSimpleL2Joint_measurable s).aestronglyMeasurable
  apply ae_of_all
  intro p
  exact Finset.single_le_sum (fun h _ => norm_nonneg (h p.1)) (s.mem_range_self p.2)

/-- Norm-square transport for the constructed finite joint path is an
actual Fubini identity. -/
theorem scalarSimpleL2Joint_integral_sq [IsFiniteMeasure ν] [SFinite μ]
    (s : SimpleFunc β (Lp ℝ 2 μ)) :
    (∫ p, (scalarSimpleL2Joint s p)^2 ∂μ.prod ν) = ∫ t, ‖s t‖^2 ∂ν := by
  have hs := scalarSimpleL2Joint_memLp (ν := ν) s
  have hsq := (memLp_two_iff_integrable_sq hs.aestronglyMeasurable).mp hs
  rw [integral_prod_symm _ hsq]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  change (∫ x, (scalarSimpleL2Joint s (x, t))^2 ∂μ) = ‖s t‖^2
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  simp only [scalarSimpleL2Joint, RCLike.inner_apply, conj_trivial, pow_two]

/-- Differences of finite joint paths have their exact time integral of
actual L² norm squares, despite the quotient's non-pointwise arithmetic. -/
theorem scalarSimpleL2Joint_sub_integral_sq [IsFiniteMeasure ν] [SFinite μ]
    (s k : SimpleFunc β (Lp ℝ 2 μ)) :
    (∫ p, (scalarSimpleL2Joint s p - scalarSimpleL2Joint k p)^2 ∂μ.prod ν) =
      ∫ t, ‖s t - k t‖^2 ∂ν := by
  have hs := (scalarSimpleL2Joint_memLp (ν := ν) s).sub (scalarSimpleL2Joint_memLp k)
  have hsq := (memLp_two_iff_integrable_sq hs.aestronglyMeasurable).mp hs
  change Integrable (fun p => (scalarSimpleL2Joint s p - scalarSimpleL2Joint k p)^2) (μ.prod ν) at hsq
  rw [integral_prod_symm _ hsq]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  change (∫ x, (scalarSimpleL2Joint s (x, t) - scalarSimpleL2Joint k (x, t))^2 ∂μ) = ‖s t - k t‖^2
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (s t) (k t)] with x hx
  rw [hx]
  simp only [scalarSimpleL2Joint, RCLike.inner_apply, conj_trivial, Pi.sub_apply, pow_two]

/-- The actual product-L² class of a finite simple L²-valued path. -/
def scalarSimpleL2JointLp [IsFiniteMeasure ν] (s : SimpleFunc β (Lp ℝ 2 μ)) : Lp ℝ 2 (μ.prod ν) :=
  (scalarSimpleL2Joint_memLp s).toLp _

theorem scalarSimpleL2JointLp_coe [IsFiniteMeasure ν] (s : SimpleFunc β (Lp ℝ 2 μ)) :
    scalarSimpleL2JointLp (ν := ν) s =ᵐ[μ.prod ν] scalarSimpleL2Joint s :=
  (scalarSimpleL2Joint_memLp s).coeFn_toLp

/-- The actual time-L² class of a finite L²-valued path. -/
def scalarSimpleL2PathLp [IsFiniteMeasure ν] (s : SimpleFunc β (Lp ℝ 2 μ)) :
    Lp (Lp ℝ 2 μ) 2 ν :=
  (SimpleFunc.memLp_of_finite_measure_preimage 2
    (fun _ _ => measure_lt_top ν _)).toLp s

theorem scalarSimpleL2PathLp_coe [IsFiniteMeasure ν] (s : SimpleFunc β (Lp ℝ 2 μ)) :
    scalarSimpleL2PathLp (ν := ν) s =ᵐ[ν] s :=
  (SimpleFunc.memLp_of_finite_measure_preimage 2
    (fun _ _ => measure_lt_top ν _)).coeFn_toLp

/-- Finite simple paths have exactly the same L² distance in the time
Bochner space and in the genuine product scalar space. -/
theorem scalarSimpleL2JointLp_dist [IsFiniteMeasure ν] [SFinite μ]
    (s k : SimpleFunc β (Lp ℝ 2 μ)) :
    dist (scalarSimpleL2JointLp (ν := ν) s) (scalarSimpleL2JointLp (ν := ν) k) =
      dist (scalarSimpleL2PathLp (ν := ν) s) (scalarSimpleL2PathLp (ν := ν) k) := by
  rw [dist_eq_norm, dist_eq_norm]
  have hprod : ‖scalarSimpleL2JointLp (ν := ν) s - scalarSimpleL2JointLp k‖^2 =
      ∫ p, (scalarSimpleL2Joint s p - scalarSimpleL2Joint k p)^2 ∂μ.prod ν := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (scalarSimpleL2JointLp (ν := ν) s) (scalarSimpleL2JointLp k),
      scalarSimpleL2JointLp_coe (ν := ν) s, scalarSimpleL2JointLp_coe (ν := ν) k] with p hp hs hk
    rw [hp]
    simp only [Pi.sub_apply, hs, hk, RCLike.inner_apply, conj_trivial, pow_two]
  have htime : ‖scalarSimpleL2PathLp (ν := ν) s - scalarSimpleL2PathLp k‖^2 =
      ∫ t, ‖s t - k t‖^2 ∂ν := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (scalarSimpleL2PathLp (ν := ν) s) (scalarSimpleL2PathLp k),
      scalarSimpleL2PathLp_coe (ν := ν) s, scalarSimpleL2PathLp_coe (ν := ν) k] with t ht hs hk
    rw [ht]
    simp only [Pi.sub_apply, hs, hk, real_inner_self_eq_norm_sq]
  nlinarith only [norm_nonneg (scalarSimpleL2JointLp (ν := ν) s - scalarSimpleL2JointLp k),
    norm_nonneg (scalarSimpleL2PathLp (ν := ν) s - scalarSimpleL2PathLp k), hprod, htime,
    scalarSimpleL2Joint_sub_integral_sq (ν := ν) s k]

/-- The finite simple core embeds isometrically into actual product L². -/
def scalarSimpleL2CoreJoint [IsFiniteMeasure ν] (s : Lp.simpleFunc (Lp ℝ 2 μ) 2 ν) :
    Lp ℝ 2 (μ.prod ν) := scalarSimpleL2JointLp (Lp.simpleFunc.toSimpleFunc s)

theorem scalarSimpleL2PathLp_toSimpleFunc [IsFiniteMeasure ν]
    (s : Lp.simpleFunc (Lp ℝ 2 μ) 2 ν) :
    scalarSimpleL2PathLp (ν := ν) (Lp.simpleFunc.toSimpleFunc s) = (s : Lp (Lp ℝ 2 μ) 2 ν) := by
  apply Lp.ext
  exact (scalarSimpleL2PathLp_coe (ν := ν) (Lp.simpleFunc.toSimpleFunc s)).trans
    (Lp.simpleFunc.toSimpleFunc_eq_toFun s)

theorem scalarSimpleL2CoreJoint_isometry [IsFiniteMeasure ν] [SFinite μ] :
    Isometry (scalarSimpleL2CoreJoint (μ := μ) (ν := ν)) := by
  apply Isometry.of_dist_eq
  intro s k
  rw [scalarSimpleL2CoreJoint, scalarSimpleL2CoreJoint, scalarSimpleL2JointLp_dist,
    scalarSimpleL2PathLp_toSimpleFunc, scalarSimpleL2PathLp_toSimpleFunc]
  rfl

/-- Every actual L²-valued L² time path has a genuine jointly measurable
product-L² representative. Its spatial slices recover the actual path for
almost every time. All representatives are constructed through finite
simple paths and completeness; no pointwise evaluation map on L² is assumed
continuous or jointly measurable. -/
theorem scalarL2Path_exists_joint [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {F : β → Lp ℝ 2 μ} (hF : MemLp F 2 ν) :
    ∃ u : α × β → ℝ, StronglyMeasurable u ∧ MemLp u 2 (μ.prod ν) ∧
      ∀ᵐ t ∂ν, (fun x => u (x,t)) =ᵐ[μ] (F t : α → ℝ) := by
  let f := hF.toLp F
  obtain ⟨a, ha, halim⟩ := mem_closure_iff_seq_limit.mp
    ((Lp.simpleFunc.dense (E := Lp ℝ 2 μ) (μ := ν) (p := 2) (by norm_num)) f)
  let s : ℕ → Lp.simpleFunc (Lp ℝ 2 μ) 2 ν := fun k => ⟨a k, ha k⟩
  let b : ℕ → Lp ℝ 2 (μ.prod ν) := fun k => scalarSimpleL2CoreJoint (s k)
  have hbc : CauchySeq b := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp halim.cauchySeq ε hε
    refine ⟨N, fun m hm k hk => ?_⟩
    have hd := (scalarSimpleL2CoreJoint_isometry (μ := μ) (ν := ν)).dist_eq (s m) (s k)
    exact hd.trans_lt (hN m hm k hk)
  obtain ⟨U,hU⟩ := cauchySeq_tendsto_of_complete hbc
  obtain ⟨ns,hns,hnsAE⟩ := (tendstoInMeasure_of_tendsto_Lp halim).exists_seq_tendsto_ae
  obtain ⟨ms,hms,hmsAE⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hU.comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  have hsteps : ∀ᵐ p ∂μ.prod ν, ∀ k : ℕ,
      b k p = scalarSimpleL2Joint (Lp.simpleFunc.toSimpleFunc (s k)) p := by
    exact ae_all_iff.mpr (fun k => scalarSimpleL2JointLp_coe (Lp.simpleFunc.toSimpleFunc (s k)))
  have hpoint : ∀ᵐ p ∂μ.prod ν,
      Tendsto (fun k => scalarSimpleL2Joint (Lp.simpleFunc.toSimpleFunc (s (ns (ms k)))) p)
        atTop (𝓝 (U p)) := by
    filter_upwards [hsteps,hmsAE] with p hp ht
    have heq : (fun k => scalarSimpleL2Joint (Lp.simpleFunc.toSimpleFunc (s (ns (ms k)))) p) =
        (fun k => b (ns (ms k)) p) := funext fun k => (hp _).symm
    rw [heq]
    exact ht
  have hpoint' : ∀ᵐ t ∂ν, ∀ᵐ x ∂μ,
      Tendsto (fun k => scalarSimpleL2Joint (Lp.simpleFunc.toSimpleFunc (s (ns (ms k)))) (x,t))
        atTop (𝓝 (U (x,t))) :=
    Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hpoint)
  have htimeSteps : ∀ᵐ t ∂ν, ∀ k : ℕ,
      Lp.simpleFunc.toSimpleFunc (s k) t = a k t :=
    ae_all_iff.mpr (fun k => Lp.simpleFunc.toSimpleFunc_eq_toFun (s k))
  refine ⟨U,Lp.stronglyMeasurable U,Lp.memLp U,?_⟩
  filter_upwards [hpoint',htimeSteps,hnsAE,hF.coeFn_toLp] with t hp hs ht hFt
  let r : ℕ → Lp ℝ 2 μ := fun k => Lp.simpleFunc.toSimpleFunc (s (ns (ms k))) t
  have hr : Tendsto r atTop (𝓝 (F t)) := by
    have hh := ht.comp hms.tendsto_atTop
    rw [hFt] at hh
    convert hh using 1
    funext k
    exact hs _
  have hp' : ∀ᵐ x ∂μ, Tendsto (fun k => r k x) atTop (𝓝 (U (x,t))) := hp
  exact tendstoInMeasure_ae_unique
    (tendstoInMeasure_of_tendsto_ae (fun k => Lp.aestronglyMeasurable (r k)) hp')
    (tendstoInMeasure_of_tendsto_Lp hr)

end Yau.LeafProofs.L19Aux

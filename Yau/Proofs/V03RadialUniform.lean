import Yau.Proofs.V03DiscScalars
import Yau.Proofs.V03LogTrace
import Yau.Proofs.V03Radial

/-! Uniform radial convergence follows from actual compact continuity.
The original strict boundary inequalities therefore persist near radius one. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem circlePoint_mem_sphere (θ : ℝ) : circlePoint θ ∈ Metric.sphere (0 : ℂ) 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using circlePoint_norm θ

theorem circlePoint_arg_of_sphere {z : ℂ} (hz : z ∈ Metric.sphere (0 : ℂ) 1) :
    circlePoint (Complex.arg z) = z := by
  have hn : ‖z‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
  simpa only [circlePoint, hn, Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I z

theorem closedDisc_radial_tendstoUniformlyOn {F : Type*} [PseudoMetricSpace F]
    {b : ℂ → F} (hb : ContinuousOn b (Metric.closedBall 0 1)) :
    TendstoUniformlyOn (fun r : ℝ => fun ζ => b ((r : ℂ) * ζ)) b
      (𝓝[Set.Icc 0 1] 1) (Metric.closedBall 0 1) := by
  have hm : Continuous (fun p : ℝ × ℂ => (p.1 : ℂ) * p.2) := by fun_prop
  have hmap : Set.MapsTo (fun p : ℝ × ℂ => (p.1 : ℂ) * p.2)
      (Set.Icc 0 1 ×ˢ Metric.closedBall 0 1) (Metric.closedBall 0 1) :=
    fun p hp => radial_maps_closedBall hp.1.1 hp.1.2 hp.2
  have hc : ContinuousOn (fun p : ℝ × ℂ => b ((p.1 : ℂ) * p.2))
      (Set.Icc 0 1 ×ˢ Metric.closedBall 0 1) := hb.comp hm.continuousOn hmap
  have hu := (isCompact_Icc.prod (isCompact_closedBall (0 : ℂ) 1)).uniformContinuousOn_of_continuous hc
  have ht := UniformContinuousOn.tendstoUniformlyOn
    (F := fun r : ℝ => fun ζ : ℂ => b ((r : ℂ) * ζ)) hu
    (by simp : (1 : ℝ) ∈ Set.Icc 0 1)
  simpa only [Complex.ofReal_one, one_mul] using ht

theorem radial_circle_lt_eventually {b : ℂ → ℝ}
    (hb : ContinuousOn b (Metric.closedBall 0 1)) {A : ℝ}
    (hA : ∀ θ, b (circlePoint θ) < A) :
    ∀ᶠ r : ℝ in 𝓝[Set.Icc 0 1] 1, ∀ θ, b ((r : ℂ) * circlePoint θ) < A := by
  obtain ⟨z, hz, hmax⟩ := (isCompact_sphere (0 : ℂ) 1).exists_isMaxOn
    ⟨1, by simp [Metric.mem_sphere]⟩ (hb.mono Metric.sphere_subset_closedBall)
  have hbz : b z < A := by
    simpa only [circlePoint_arg_of_sphere hz] using hA (Complex.arg z)
  have hm : 0 < (A - b z) / 2 := by linarith
  have ht := (Metric.tendstoUniformlyOn_iff.mp (closedDisc_radial_tendstoUniformlyOn hb))
    ((A - b z) / 2) hm
  filter_upwards [ht] with r hr
  intro θ
  have hd := hr (circlePoint θ) (circlePoint_mem_closedBall θ)
  have hupper : b (circlePoint θ) ≤ b z := hmax (circlePoint_mem_sphere θ)
  rw [Real.dist_eq] at hd
  have hh := (abs_lt.mp hd).1
  linarith

variable {n q : ℕ} {X : KahlerManifold n}

theorem radial_boundaryRegion_eventually {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    ∀ᶠ r : ℝ in 𝓝[Set.Icc 0 1] 1,
      ∀ θ, (radialVariationDisc F r).f (circlePoint θ) ∈ boundaryRegion d j := by
  have hu := (cotangentDisc_smoothFn_contDiffOn hd.2.2.2.1.1 hF.1).continuousOn
  have h0 : d.h 0 = X.metric.form := hd.2.2.1.1.1.1
  have hN : ContinuousOn (fun ζ => dualNorm (d.h 0) (F.f ζ).1 (F.f ζ).2)
      (Metric.closedBall 0 1) := by
    rw [h0]
    exact (cotangentDisc_dualNorm_contDiffOn X.metric hF.1).continuousOn
  have hbase := radial_circle_lt_eventually hu (fun θ => (hF.2.2.2.2.2.2.2.1 θ).1)
  have hfiber := radial_circle_lt_eventually hN (fun θ => (hF.2.2.2.2.2.2.2.1 θ).2)
  filter_upwards [hbase, hfiber] with r hrb hrf
  exact fun θ => ⟨hrb θ, hrf θ⟩

end Yau.Blueprint.V03Proof

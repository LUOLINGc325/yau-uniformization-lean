import Yau.Proofs.V02FlowNativeCharts
import Yau.Proofs.V02FlowUniqueness
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue

/-! Native overlap uniqueness by local ODE uniqueness and closed continuation. -/

open scoped Manifold Topology ContDiff NNReal Matrix
open Filter Metric Set

noncomputable section
namespace Yau.Blueprint.V02FlowProof
open Yau Yau.Blueprint V03Proof

variable {n : ℕ} {M : ComplexManifold n} [T2Space (NativeCotangentPoint M)]

theorem native_complex_ode_unique_on_ball
    {Z : CotangentPoint M → CotangentIndex n → ℂ}
    (hZ : ∀ x i, DifferentiableOn ℂ
      (fun z => (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        Z (cotangentChartInv x z)) i) (cotangentTarget x))
    {R : ℝ} {u v : ℂ → NativeCotangentPoint M}
    (hu : NativeFieldIntegralCurve Z u (ball (0 : ℂ) R))
    (hv : NativeFieldIntegralCurve Z v (ball (0 : ℂ) R))
    (hzero : u 0 = v 0) : EqOn u v (ball (0 : ℂ) R) := by
  intro t ht
  let I := Icc (0 : ℝ) 1
  letI : PreconnectedSpace I := Subtype.preconnectedSpace isPreconnected_Icc
  have hrad : ∀ s ∈ I, (s : ℂ) * t ∈ ball (0 : ℂ) R := by
    intro s hs
    rw [mem_ball, dist_zero_right]
    exact (norm_radial_time_le hs t).trans_lt (by simpa using ht)
  have hcR : Continuous (fun s : ℝ => (s : ℂ) * t) := Complex.continuous_ofReal.mul_const t
  have huc : ∀ s ∈ I, ContinuousAt (fun r : ℝ => u ((r : ℂ) * t)) s := by
    intro s hs
    have huAt : ContinuousAt u ((s : ℂ) * t) :=
      hu.1.continuousAt (isOpen_ball.mem_nhds (hrad s hs))
    exact huAt.comp_of_eq (hcR.continuousAt (x := s)) rfl
  have hvc : ∀ s ∈ I, ContinuousAt (fun r : ℝ => v ((r : ℂ) * t)) s := by
    intro s hs
    have hvAt : ContinuousAt v ((s : ℂ) * t) :=
      hv.1.continuousAt (isOpen_ball.mem_nhds (hrad s hs))
    exact hvAt.comp_of_eq (hcR.continuousAt (x := s)) rfl
  let A : Set I := {s | u ((s.1 : ℂ) * t) = v ((s.1 : ℂ) * t)}
  have hclosed : IsClosed A := isClosed_eq
    (hu.1.comp_continuous (hcR.comp continuous_subtype_val) (fun s => hrad s.1 s.2))
    (hv.1.comp_continuous (hcR.comp continuous_subtype_val) (fun s => hrad s.1 s.2))
  have hopen : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro s hs
    change u ((s.1 : ℂ) * t) = v ((s.1 : ℂ) * t) at hs
    let x := (u ((s.1 : ℂ) * t)).val.1
    let e := nativeCotangentChartHomeomorph x
    have hxs : u ((s.1 : ℂ) * t) ∈ e.source := mem_extChartAt_source _
    have hxv : v ((s.1 : ℂ) * t) ∈ e.source := by rw [← hs]; exact hxs
    have htarget := e.map_source hxs
    have hfield : ContDiffAt ℂ 1 (cotangentChartField Z x)
        (cotangentChart x (u ((s.1 : ℂ) * t)).val) :=
      ((cotangentChartField_contDiffOn hZ x).contDiffAt
        (((isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ).mem_nhds htarget)).of_le
          (by simp)
    obtain ⟨L, B, hB, hLip⟩ := hfield.exists_lipschitzOnWith
    have hscaled : LipschitzOnWith (‖t‖₊ * L) (fun z => t • cotangentChartField Z x z) B := by
      apply LipschitzOnWith.of_dist_le_mul
      intro a ha b hb
      rw [dist_eq_norm, ← smul_sub, norm_smul, NNReal.coe_mul, coe_nnnorm, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [dist_eq_norm] using (hLip.dist_le_mul a ha b hb)) (norm_nonneg t)
    have hcu := huc s.1 s.2
    have hcv := hvc s.1 s.2
    have hsourceU : ∀ᶠ r : ℝ in 𝓝 s.1, u ((r : ℂ) * t) ∈ e.source :=
      hcu.preimage_mem_nhds (e.open_source.mem_nhds hxs)
    have hsourceV : ∀ᶠ r : ℝ in 𝓝 s.1, v ((r : ℂ) * t) ∈ e.source :=
      hcv.preimage_mem_nhds (e.open_source.mem_nhds hxv)
    have hcoordU := (e.continuousOn.continuousAt (e.open_source.mem_nhds hxs)).comp_of_eq hcu rfl
    have hcoordV := (e.continuousOn.continuousAt (e.open_source.mem_nhds hxv)).comp_of_eq hcv rfl
    have hBU : ∀ᶠ r : ℝ in 𝓝 s.1, e (u ((r : ℂ) * t)) ∈ B := hcoordU.preimage_mem_nhds hB
    have hBV : ∀ᶠ r : ℝ in 𝓝 s.1, e (v ((r : ℂ) * t)) ∈ B :=
      hcoordV.preimage_mem_nhds (by
        change B ∈ 𝓝 (e (v ((s.1 : ℂ) * t)))
        rw [← hs]
        exact hB)
    have htime : ∀ᶠ r : ℝ in 𝓝 s.1, (r : ℂ) * t ∈ ball (0 : ℂ) R :=
      hcR.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds (hrad s.1 s.2))
    have hdu : ∀ᶠ r : ℝ in 𝓝 s.1,
        HasDerivAt (fun a : ℝ => e (u ((a : ℂ) * t)))
          (t • cotangentChartField Z x (e (u ((r : ℂ) * t)))) r ∧
        e (u ((r : ℂ) * t)) ∈ B := by
      filter_upwards [htime, hsourceU, hBU] with r hr hsource hB'
      exact ⟨HasDerivAt.radial_real (hu.2 _ hr x hsource), hB'⟩
    have hdv : ∀ᶠ r : ℝ in 𝓝 s.1,
        HasDerivAt (fun a : ℝ => e (v ((a : ℂ) * t)))
          (t • cotangentChartField Z x (e (v ((r : ℂ) * t)))) r ∧
        e (v ((r : ℂ) * t)) ∈ B := by
      filter_upwards [htime, hsourceV, hBV] with r hr hsource hB'
      exact ⟨HasDerivAt.radial_real (hv.2 _ hr x hsource), hB'⟩
    have heq := ODE_solution_unique_of_eventually
      (v := fun _ z => t • cotangentChartField Z x z) (s := fun _ => B)
      (Eventually.of_forall (fun _ => hscaled)) hdu hdv (congrArg e hs)
    have hnative : ∀ᶠ r : ℝ in 𝓝 s.1, u ((r : ℂ) * t) = v ((r : ℂ) * t) := by
      filter_upwards [heq, hsourceU, hsourceV] with r hr hu' hv'
      exact e.injOn hu' hv' hr
    exact (continuous_subtype_val.tendsto s).eventually hnative
  have hnonempty : A.Nonempty := ⟨⟨0, by simp [I]⟩, by simpa [A] using hzero⟩
  have hall : A = univ := (show IsClopen A from ⟨hclosed, hopen⟩).eq_univ hnonempty
  have hfinal : (⟨1, by simp [I]⟩ : I) ∈ A := hall ▸ mem_univ _
  simpa only [A, Complex.ofReal_one, one_mul, mem_setOf_eq] using hfinal

end Yau.Blueprint.V02FlowProof

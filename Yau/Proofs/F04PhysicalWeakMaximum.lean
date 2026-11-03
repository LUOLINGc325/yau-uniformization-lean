import Yau.Proofs.F04PhysicalShiftTimeChain
import Yau.Proofs.F04PositiveOrder
import Yau.LeafProofs.L16GalerkinEnergy

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace ENNReal
noncomputable section
namespace Yau.F04Proof
open Yau.Proofs.F03Aux Yau.LeafProofs.L03 Yau.HeatConcreteBindings
  Yau.LeafProofs.L16HilbertTimeRegularization
variable {n : ℕ} {M : ComplexManifold n}

/-- Weak comparison for the actual shifted supported test. The residual
inequality is tested only against that constructed element of the original V. -/
theorem dirichlet_shift_posPart_physical_weak_maximum
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
    {U : ℝ → DirichletEnergy g μ hμ O}
    {R : ℝ → StrongDual ℝ (DirichletEnergy g μ hμ O)}
    (hU : MemLp U 2 (volume.restrict (Ioo 0 T)))
    (hR : MemLp R 2 (volume.restrict (Ioo 0 T)))
    (hw : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ioo 0 T →
      (∫ t in Ioo 0 T, deriv η t • hilbertEmbedding (dirichletL2 g μ hμ O) (U t)) =
        -(∫ t in Ioo 0 T, η t • R t))
    (a : ℝ → Lp ℝ 2 (μ.restrict O)) (ha : ContinuousOn a (Icc 0 T))
    (hae : ∀ᵐ t ∂volume.restrict (Ioo 0 T), dirichletL2 g μ hμ O (U t) = a t)
    (K : ℝ) (hK0 : 0 ≤ K)
    (hinit : ∀ᵐ x ∂μ.restrict O, a 0 x ≤ b 0 x)
    (hbound : ∀ᵐ t ∂volume.restrict (Ioo 0 T),
      let w := dirichletShiftPosPart g μ hμ O hO (r t) (hr t) (hr0 t) (hr2 t) (hdr2 t) (U t)
      R t w - inner ℝ (derivWithin b (Icc 0 T) t) (dirichletL2 g μ hμ O w) ≤ K * ‖Lp.posPart (a t - b t)‖ ^ 2) :
    ∀ t ∈ Icc 0 T, ∀ᵐ x ∂μ.restrict O, a t x ≤ b t x := by
  let W := fun t => dirichletShiftPosPart g μ hμ O hO (r t) (hr t) (hr0 t) (hr2 t) (hdr2 t) (U t)
  let F := fun t => R t (W t) - inner ℝ (derivWithin b (Icc 0 T) t) (dirichletL2 g μ hμ O (W t))
  let y := fun t => ‖Lp.posPart (a t - b t)‖ ^ 2
  have hy : ContinuousOn y (Icc 0 T) :=
    ((Lp.continuous_posPart.comp_continuousOn (ha.sub hb.continuousOn)).norm).pow 2
  have hy0 : y 0 = 0 := by
    dsimp only [y]
    rw [(lp_posPart_sub_eq_zero_iff (μ.restrict O) (a 0) (b 0)).mpr hinit, norm_zero]
    norm_num
  have hc := dirichlet_shift_posPart_physical_time_chain g hK μ hμ O hO r hr hr0 hr2 hdr2 hRH hRD
    hT b hb hbval hU hR hw a ha hae
  have hFi : IntegrableOn F (Ioo 0 T) := hc.1.sub hc.2.1
  have hi : ∀ t ∈ Icc 0 T, y t ≤ (2 * K + 1) * (∫ s in (0 : ℝ)..t, y s) + 0 := by
    intro t ht
    have hyi : IntervalIntegrable y volume 0 t :=
      (hy.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
    have hFit : IntegrableOn F (Ioo 0 t) := hFi.mono_set (Ioo_subset_Ioo le_rfl ht.2)
    have hyit : IntegrableOn y (Ioo 0 t) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mp hyi
    have hbnd : F ≤ᵐ[volume.restrict (Ioo 0 t)] (fun s => K * y s) :=
      hbound.filter_mono (ae_mono (Measure.restrict_mono (Ioo_subset_Ioo le_rfl ht.2) le_rfl))
    have hcmp := integral_mono_ae hFit (hyit.const_mul K) hbnd
    rw [integral_const_mul] at hcmp
    have hint : (∫ s in (0 : ℝ)..t, F s) ≤ K * (∫ s in (0 : ℝ)..t, y s) := by
      simpa only [intervalIntegral.integral_of_le ht.1, integral_Ioc_eq_integral_Ioo] using hcmp
    have hch := hc.2.2 0 ⟨le_rfl, hT.le⟩ t ht
    change y t - y 0 = 2 * ∫ s in (0 : ℝ)..t, F s at hch
    rw [hy0, sub_zero] at hch
    have hint0 : 0 ≤ ∫ s in (0 : ℝ)..t, y s :=
      intervalIntegral.integral_nonneg_of_forall ht.1 (fun _ => sq_nonneg _)
    nlinarith
  have hz := Yau.LeafProofs.L16Aux.energy_integral_gronwall_on hT.le (by positivity : 0 < 2 * K + 1) hy hi
  intro t ht
  have hs : y t = 0 := le_antisymm (by simpa only [mul_zero] using hz t ht) (sq_nonneg _)
  have hn : ‖Lp.posPart (a t - b t)‖ = 0 := by
    change ‖Lp.posPart (a t - b t)‖ ^ 2 = 0 at hs
    nlinarith [norm_nonneg (Lp.posPart (a t - b t))]
  exact (lp_posPart_sub_eq_zero_iff (μ.restrict O) (a t) (b t)).mp (norm_eq_zero.mp hn)

end Yau.F04Proof

import Yau.Proofs.F04SupportedChartOrder
import Yau.Proofs.F04ZeroPastLp
import Yau.LeafProofs.L19HeatRegularitySlices
import Yau.LeafProofs.L16WeakLocalization

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.Proofs.F03Aux Yau.LeafProofs.L19Aux Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- The already proved actual-volume chart order transport also
 transports equality of arbitrary supported representatives. -/
theorem chart_ae_eq_of_supported_ae_eq
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) (c : M.Carrier)
    {O : Set (Space n)} (hO : IsOpen O) (hOC : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget c) (hMap : chartInv c '' O ⊆ Ω)
    {f k : M.Carrier → ℝ} (hfk : f =ᵐ[μ.restrict Ω] k) :
    (fun z => f (chartInv c z)) =ᵐ[volume.restrict O] (fun z => k (chartInv c z)) := by
  have hl := chart_ae_le_of_supported_ae_le g μ hμ Ω hΩ c hO hOC hOt hMap
    (hfk.mono (fun _ hx => hx.le))
  have hr := chart_ae_le_of_supported_ae_le g μ hμ Ω hΩ c hO hOC hOt hMap
    (hfk.mono (fun _ hx => hx.ge))
  filter_upwards [hl,hr] with z hz₁ hz₂
  exact le_antisymm hz₁ hz₂

/-- Genuine compact smooth-slice L2 continuity and the ORIGINAL continuous
 pivot trace upgrade AE-time chart identities to EVERY positive time.
 This is a generic actual-L2 argument, independent of any heat producer. -/
theorem supported_chart_smoothSlice_every_time
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) (c : M.Carrier)
    {O V : Set (Space n)} (hO : IsOpen O) (hOC : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget c) (hV : IsOpen V) (hVC : IsCompact (closure V))
    (hVO : closure V ⊆ O) (hMap : chartInv c '' V ⊆ Ω) {l r : ℝ}
    (A : ℝ → Lp ℝ 2 (μ.restrict Ω)) (hAc : ContinuousOn A (Ioo l r))
    {v : Point n → ℝ} (hv : ContDiffOn ℝ ∞ v (O ×ˢ Ioo l r))
    (hAE : ∀ᵐ t ∂volume.restrict (Ioo l r), (fun z => v (z,t)) =ᵐ[volume.restrict O]
      scalarEnergy_chartRestrictionCLM g μ hμ c hO hOC hOt (l2ZeroExtension μ Ω hΩ (A t))) :
    ∀ t ∈ Ioo l r, (fun z => v (z,t)) =ᵐ[volume.restrict V]
      (fun z => A t (chartInv c z)) := by
  obtain ⟨D,hDc,hD⟩ := scalarSmoothSlice_exists_continuousLp hO hV hVC hVO hv
  let R := scalarEnergy_chartRestrictionCLM g μ hμ c hV hVC
    (hVO.trans (subset_closure.trans hOt))
  let B := fun t => R (l2ZeroExtension μ Ω hΩ (A t))
  have hBc : ContinuousOn B (Ioo l r) :=
    R.continuous.comp_continuousOn ((l2ZeroExtension μ Ω hΩ).continuous.comp_continuousOn hAc)
  have hDB : D =ᵐ[volume.restrict (Ioo l r)] B := by
    filter_upwards [hAE,ae_restrict_mem measurableSet_Ioo] with t ht htI
    apply Lp.ext
    have hVS : V ⊆ O := subset_closure.trans hVO
    have hvV := ae_restrict_of_ae_restrict_of_subset hVS ht
    have ho := ae_restrict_of_ae_restrict_of_subset hVS
      (scalarEnergy_chartRestrictionCLM_coe g μ hμ c hO hOC hOt (l2ZeroExtension μ Ω hΩ (A t)))
    have hi := scalarEnergy_chartRestrictionCLM_coe g μ hμ c hV hVC
      (hVO.trans (subset_closure.trans hOt)) (l2ZeroExtension μ Ω hΩ (A t))
    filter_upwards [hD t htI,hvV,ho,hi] with z hd hvz hoz hiz
    exact hd.trans (hvz.trans (hoz.trans hiz.symm))
  have hAll := Measure.eqOn_open_of_ae_eq hDB isOpen_Ioo hDc hBc
  intro t ht
  have hDAE := Lp.ext_iff.mp (hAll ht)
  have hZA : (l2ZeroExtension μ Ω hΩ (A t) : M.Carrier → ℝ) =ᵐ[μ]
      Ω.indicator (A t : M.Carrier → ℝ) := extendL2_coe μ Ω hΩ (A t)
  have hZ := scalarEnergy_chart_ae_eq g μ hμ c hV hVC (hVO.trans (subset_closure.trans hOt)) hZA
  filter_upwards [hD t ht,hDAE,scalarEnergy_chartRestrictionCLM_coe g μ hμ c hV hVC
    (hVO.trans (subset_closure.trans hOt)) (l2ZeroExtension μ Ω hΩ (A t)),hZ,
    ae_restrict_mem hV.measurableSet] with z hDz hEq hR hZz hz
  exact hDz.symm.trans (hEq.trans (hR.trans (hZz.trans (indicator_of_mem (hMap ⟨z,hz,rfl⟩) _))))

/-- Actual joint chart representatives of the genuine supported energy
 path identify the ORIGINAL continuous trace at every positive time. -/
theorem supported_chart_smoothSlice_of_joint
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) (c : M.Carrier)
    {O V : Set (Space n)} (hO : IsOpen O) (hOC : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget c) (hV : IsOpen V) (hVC : IsCompact (closure V))
    (hVO : closure V ⊆ O) (hMap : chartInv c '' V ⊆ Ω) {S : ℝ}
    (U : ℝ → DirichletEnergy g μ hμ Ω) (A : ℝ → Lp ℝ 2 (μ.restrict Ω))
    (hAc : ContinuousOn A (Ioo 0 S)) {u v : Point n → ℝ}
    (hv : ContDiffOn ℝ ∞ v (O ×ˢ Ioo 0 S))
    (hAE : u =ᵐ[productVolume O (Ioo 0 S)] v)
    (hSlices : ∀ᵐ t ∂volume.restrict (Ioo 0 S),
      (fun z => u (z,t)) =ᵐ[volume.restrict O]
        scalarEnergy_chartRestrictionCLM g μ hμ c hO hOC hOt (scalarEnergyL2 g μ hμ (U t).val))
    (hAJ : ∀ᵐ t ∂volume.restrict (Ioo 0 S), A t = dirichletL2 g μ hμ Ω (U t)) :
    ∀ t ∈ Ioo 0 S, (fun z => v (z,t)) =ᵐ[volume.restrict V]
      (fun z => A t (chartInv c z)) := by
  have hs : ∀ᵐ t ∂volume.restrict (Ioo 0 S),
      (fun z => u (z,t)) =ᵐ[volume.restrict O] (fun z => v (z,t)) :=
    Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hAE)
  apply supported_chart_smoothSlice_every_time g μ hμ Ω hΩ c hO hOC hOt hV hVC hVO hMap A hAc hv
  filter_upwards [hs,hSlices,hAJ] with t ht hst hJ
  have hZ : l2ZeroExtension μ Ω hΩ (A t) = scalarEnergyL2 g μ hμ (U t).val := by
    rw [hJ,dirichletL2_zeroExtension]
  rw [hZ]
  filter_upwards [ht,hst] with z hz hR
  exact hz.symm.trans hR

/-- The ORIGINAL zero trace identifies the genuine zero-initial
 representative with the continuous pivot at every CLOSED-slab time.
 Positive times follow from actual L2 continuity; zero uses A0=0. -/
theorem supported_chart_smoothSlice_closed_of_joint
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) (c : M.Carrier)
    {O V : Set (Space n)} (hO : IsOpen O) (hOC : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget c) (hV : IsOpen V) (hVC : IsCompact (closure V))
    (hVO : closure V ⊆ O) (hMap : chartInv c '' V ⊆ Ω) {S T : ℝ} (hTS : T < S)
    (U : ℝ → DirichletEnergy g μ hμ Ω) (A : ℝ → Lp ℝ 2 (μ.restrict Ω))
    (hAc : ContinuousOn A (Ioo 0 S)) (hA0 : A 0 = 0) {u v : Point n → ℝ}
    (hv : ContDiffOn ℝ ∞ v (O ×ˢ Ioo 0 S))
    (hAE : u =ᵐ[productVolume O (Ioo 0 S)] v)
    (hSlices : ∀ᵐ t ∂volume.restrict (Ioo 0 S),
      (fun z => u (z,t)) =ᵐ[volume.restrict O]
        scalarEnergy_chartRestrictionCLM g μ hμ c hO hOC hOt (scalarEnergyL2 g μ hμ (U t).val))
    (hAJ : ∀ᵐ t ∂volume.restrict (Ioo 0 S), A t = dirichletL2 g μ hμ Ω (U t)) :
    ∀ t ∈ Icc 0 T, (fun z => zeroPast v (z,t)) =ᵐ[volume.restrict V]
      (fun z => A t (chartInv c z)) := by
  have hPos := supported_chart_smoothSlice_of_joint g μ hμ Ω hΩ c hO hOC hOt hV hVC hVO hMap
    U A hAc hv hAE hSlices hAJ
  intro t ht
  by_cases htp : 0 < t
  · filter_upwards [hPos t ⟨htp,ht.2.trans_lt hTS⟩] with z hz
    rw [zeroPast_of_pos v htp]
    exact hz
  · have ht0 : t = 0 := le_antisymm (le_of_not_gt htp) ht.1
    subst t
    have hAZ : (A 0 : M.Carrier → ℝ) =ᵐ[μ.restrict Ω] (fun _ => 0) := by
      rw [hA0]
      exact Lp.coeFn_zero ℝ 2 (μ.restrict Ω)
    have hz := chart_ae_eq_of_supported_ae_eq g μ hμ Ω hΩ c hV hVC
      (hVO.trans (subset_closure.trans hOt)) hMap hAZ
    filter_upwards [hz] with z hzz
    rw [zeroPast_of_nonpos v le_rfl]
    exact hzz.symm

end Yau.F04Proof

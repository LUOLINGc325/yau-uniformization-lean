import Yau.LeafProofs.L23FieldMetricConnection
import Yau.LeafProofs.L23TensorAlgebra

/-! The genuine local chart spray and its conserved energy under MetricSmooth. -/
noncomputable section
open MeasureTheory Filter Bundle
open scoped Topology Manifold ENNReal Matrix ContDiff
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 200000

theorem chartGeodesicSpray_contDiffOn (h : HermitianField M) (hh : MetricSmooth h) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (chartGeodesicSpray h x) (chartTarget x ×ˢ Set.univ) := by
  have hΓ (c a b : RIdx n) : ContDiffOn ℝ ∞
      (fun q : ComplexVector n × ComplexVector n => christoffel h x q.1 c a b)
      (chartTarget x ×ˢ Set.univ) :=
    (christoffel_contDiffOn h hh x c a b).comp contDiffOn_fst (fun _ hq => hq.1)
  have hcoord (a : RIdx n) : ContDiffOn ℝ ∞
      (fun q : ComplexVector n × ComplexVector n => realCoord q.2 a)
      (chartTarget x ×ˢ Set.univ) :=
    ((contDiff_realCoord a).comp contDiff_snd).contDiffOn
  apply contDiffOn_snd.prodMk
  apply ContDiffOn.neg
  apply ContDiffOn.sum
  intro c _
  apply ContDiffOn.fun_smul _ contDiffOn_const
  apply ContDiffOn.sum
  intro a _
  apply ContDiffOn.sum
  intro b _
  exact ((hΓ c a b).mul (hcoord a)).mul (hcoord b)

theorem exists_local_chartGeodesic (h : HermitianField M) (hh : MetricSmooth h) (x : M.Carrier)
    (z v : ComplexVector n) (hz : z ∈ chartTarget x) (t₀ : ℝ) :
    ∃ η : ℝ → ComplexVector n × ComplexVector n, η t₀ = (z, v) ∧
      ∃ ε > (0 : ℝ), ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
        (η t).1 ∈ chartTarget x ∧ HasDerivAt η (chartGeodesicSpray h x (η t)) t := by
  have hO : IsOpen (chartTarget x ×ˢ (Set.univ : Set (ComplexVector n))) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  have hq : (z, v) ∈ chartTarget x ×ˢ (Set.univ : Set (ComplexVector n)) := ⟨hz, Set.mem_univ _⟩
  have hs := ((chartGeodesicSpray_contDiffOn h hh x).contDiffAt (hO.mem_nhds hq)).of_le
    (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)
  obtain ⟨η, hη, ε, hε, hsol⟩ :=
    hs.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀
  have hc : ContinuousAt η t₀ := (hsol t₀ (by constructor <;> linarith)).continuousAt
  have hmem : η ⁻¹' (chartTarget x ×ˢ (Set.univ : Set (ComplexVector n))) ∈ 𝓝 t₀ :=
    hc.preimage_mem_nhds (hη.symm ▸ hO.mem_nhds hq)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨η, hη, min ε δ, lt_min hε hδ, ?_⟩
  intro t ht
  have htε : t ∈ Set.Ioo (t₀ - ε) (t₀ + ε) :=
    ⟨by linarith [ht.1, ht.2, min_le_left ε δ], by linarith [ht.1, ht.2, min_le_left ε δ]⟩
  have htδ : t ∈ Metric.ball t₀ δ := by
    rw [Real.ball_eq_Ioo]
    exact ⟨by linarith [ht.1, ht.2, min_le_right ε δ], by linarith [ht.1, ht.2, min_le_right ε δ]⟩
  exact ⟨(hsub htδ).1, hsol t htε⟩

theorem realCurveVelocity_chartGeodesic (h : HermitianField M) (hh : MetricSmooth h) (x : M.Carrier)
    (η : ℝ → ComplexVector n × ComplexVector n) {t : ℝ}
    (hz : (η t).1 ∈ chartTarget x)
    (hη : HasDerivAt η (chartGeodesicSpray h x (η t)) t) :
    realCurveVelocity (fun s => chartInv x (η s).1) t = realChartVec x (η t).1 (η t).2 := by
  letI := manifold_realSmooth M
  have hi := (contMDiffAt_chartInv_real x (η t).1 hz).mdifferentiableAt (by simp)
  have hp : HasDerivAt (fun s => (η s).1) (η t).2 t := by
    convert! hη.hasFDerivAt.fst.hasDerivAt using 1
    simp [chartGeodesicSpray]
  have hpd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) (fun s => (η s).1) t :=
    hp.differentiableAt.mdifferentiableAt
  unfold realCurveVelocity
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n)
    (chartInv x ∘ fun s => (η s).1) t
      ((tangentSpaceCastModel 𝓘(ℝ, ℝ) t).symm 1) = _
  rw [mfderiv_comp t hi hpd, ContinuousLinearMap.comp_apply,
    mfderiv_eq_fderiv, hp.hasFDerivAt.fderiv]
  simp [realChartVec, NormedSpace.fromTangentSpace, mfld_simps]

theorem chartGeodesicEnergy_contDiffOn (h : HermitianField M) (hh : MetricSmooth h) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (chartGeodesicEnergy h x) (chartTarget x ×ˢ Set.univ) := by
  have hB := (realMetricInChart_smooth h hh x).comp contDiffOn_fst
    (show Set.MapsTo (fun q : ComplexVector n × ComplexVector n => q.1)
      (chartTarget x ×ˢ Set.univ) (chartTarget x) from fun _ hq => hq.1)
  exact (hB.clm_apply contDiffOn_snd).clm_apply contDiffOn_snd

theorem chartGeodesicEnergy_fderiv_spray (h : HermitianField M) (hh : MetricSmooth h) (x : M.Carrier)
    (q : ComplexVector n × ComplexVector n) (hq : q.1 ∈ chartTarget x) :
    fderiv ℝ (chartGeodesicEnergy h x) q (chartGeodesicSpray h x q) = 0 := by
  have hB := ((realMetricInChart_smooth h hh x).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hq)).differentiableAt (by simp)
  have hG := hB.hasFDerivAt.comp q (hasFDerivAt_fst (p := q))
  have hV := hasFDerivAt_snd (𝕜 := ℝ) (p := q)
  have hE := (hG.clm_apply hV).clm_apply hV
  change fderiv ℝ (fun p : ComplexVector n × ComplexVector n =>
    ((realMetricInChart h x ∘ Prod.fst) p) p.2 p.2) q (chartGeodesicSpray h x q) = 0
  rw [hE.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,
    Function.comp_apply, chartGeodesicSpray]
  change realMetricInChart h x q.1 q.2 (chartGeodesicAcceleration h x q.1 q.2) +
    (realMetricInChart h x q.1 (chartGeodesicAcceleration h x q.1 q.2) q.2 +
      fderiv ℝ (realMetricInChart h x) q.1 q.2 q.2 q.2) = 0
  rw [realMetricInChart_connection_compatibility h hh x q.1 hq q.2 q.2 q.2,
    chartGeodesicAcceleration_eq]
  simp only [map_neg, neg_apply]
  ring

theorem chartGeodesicEnergy_hasDerivAt (h : HermitianField M) (hh : MetricSmooth h) (x : M.Carrier)
    (η : ℝ → ComplexVector n × ComplexVector n) {t : ℝ}
    (hz : (η t).1 ∈ chartTarget x)
    (hη : HasDerivAt η (chartGeodesicSpray h x (η t)) t) :
    HasDerivAt (fun s => chartGeodesicEnergy h x (η s)) 0 t := by
  have hO : IsOpen (chartTarget x ×ˢ (Set.univ : Set (ComplexVector n))) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  have hE := ((chartGeodesicEnergy_contDiffOn h hh x).contDiffAt
    (hO.mem_nhds ⟨hz, Set.mem_univ _⟩)).differentiableAt (by simp)
  have hs := hE.hasFDerivAt.comp_hasDerivAt t hη
  rw [chartGeodesicEnergy_fderiv_spray h hh x (η t) hz] at hs
  exact hs

theorem chartGeodesicEnergy_constant (h : HermitianField M) (hh : MetricSmooth h) (x : M.Carrier)
    (η : ℝ → ComplexVector n × ComplexVector n) {a b s t : ℝ}
    (hη : ∀ r ∈ Set.Ioo a b, (η r).1 ∈ chartTarget x ∧
      HasDerivAt η (chartGeodesicSpray h x (η r)) r)
    (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) :
    chartGeodesicEnergy h x (η s) = chartGeodesicEnergy h x (η t) := by
  apply isOpen_Ioo.is_const_of_deriv_eq_zero
    (f := fun r => chartGeodesicEnergy h x (η r)) (convex_Ioo a b).isPreconnected
  · intro r hr
    exact (chartGeodesicEnergy_hasDerivAt h hh x η (hη r hr).1 (hη r hr).2).differentiableAt.differentiableWithinAt
  · intro r hr
    exact (chartGeodesicEnergy_hasDerivAt h hh x η (hη r hr).1 (hη r hr).2).deriv
  · exact hs
  · exact ht

theorem chartGeodesicEnergy_eq_actual_speed_sq (h : HermitianField M) (hh : MetricSmooth h) (x : M.Carrier)
    (η : ℝ → ComplexVector n × ComplexVector n) {t : ℝ}
    (hz : (η t).1 ∈ chartTarget x)
    (hη : HasDerivAt η (chartGeodesicSpray h x (η t)) t) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup h y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace h y
    chartGeodesicEnergy h x (η t) =
      ‖realCurveVelocity (fun s => chartInv x (η s).1) t‖ ^ 2 := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup h y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace h y
  rw [← real_inner_self_eq_norm_sq, realCurveVelocity_chartGeodesic h hh x η hz hη]
  rfl

theorem chartGeodesic_contDiffOn_Icc (h : HermitianField M) (hh : MetricSmooth h) (x : M.Carrier)
    (η : ℝ → ComplexVector n × ComplexVector n) {a b : ℝ}
    (hη : ∀ r ∈ Set.Icc a b, (η r).1 ∈ chartTarget x ∧
      HasDerivAt η (chartGeodesicSpray h x (η r)) r) :
    ContDiffOn ℝ ∞ η (Set.Icc a b) := by
  have hf := (chartGeodesicSpray_contDiffOn h hh x).comp contDiffOn_snd
    (show Set.MapsTo Prod.snd (Set.Icc a b ×ˢ (chartTarget x ×ˢ Set.univ))
      (chartTarget x ×ˢ Set.univ) from fun _ hq => hq.2)
  exact ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt (n := (⊤ : ℕ∞))
    (f := fun (_r : ℝ) (q : ComplexVector n × ComplexVector n) => chartGeodesicSpray h x q)
    (u := chartTarget x ×ˢ Set.univ) (α := η) hf
    (fun r hr => (hη r hr).2.hasDerivWithinAt)
    (fun r hr => ⟨(hη r hr).1, Set.mem_univ _⟩)

theorem chartGeodesic_curve_contMDiffOn_Icc (h : HermitianField M) (hh : MetricSmooth h) (x : M.Carrier)
    (η : ℝ → ComplexVector n × ComplexVector n) {a b : ℝ}
    (hη : ∀ r ∈ Set.Icc a b, (η r).1 ∈ chartTarget x ∧
      HasDerivAt η (chartGeodesicSpray h x (η r)) r) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) ∞
      (fun r => chartInv x (η r).1) (Set.Icc a b) := by
  letI := manifold_realSmooth M
  have hfst := contDiff_fst.comp_contDiffOn (chartGeodesic_contDiffOn_Icc h hh x η hη)
  exact (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, ComplexVector n)) (n := ∞) x).comp
    hfst.contMDiffOn (fun r hr => (hη r hr).1)

theorem realTangentChartChange_fderiv_spray (h : HermitianField M) (hh : MetricSmooth h) (a b : M.Carrier)
    (q : ComplexVector n × ComplexVector n) (hq : q.1 ∈ chartTarget a)
    (hy : chartInv a q.1 ∈ (extChartAt (ComplexModel n) b).source) :
    fderiv ℝ (realTangentChartChange a b) q (chartGeodesicSpray h a q) =
      chartGeodesicSpray h b (realTangentChartChange a b q) := by
  have hψ := realChartChange_contDiffAt a b hq hy
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ (realChartChange a b)) q.1 := hψ.fderiv_right (by simp)
  have hF := (hψ.differentiableAt (by simp)).hasFDerivAt.comp q (hasFDerivAt_fst (p := q))
  have hV := ((hD.differentiableAt (by simp)).hasFDerivAt.comp q
    (hasFDerivAt_fst (p := q))).clm_apply (hasFDerivAt_snd (p := q))
  have hJet := hF.prodMk hV
  change fderiv ℝ (fun p : ComplexVector n × ComplexVector n =>
    ((realChartChange a b ∘ Prod.fst) p, ((fderiv ℝ (realChartChange a b) ∘ Prod.fst) p) p.2)) q
      (chartGeodesicSpray h a q) = _
  rw [hJet.fderiv]
  change (fderiv ℝ (realChartChange a b) q.1 q.2,
    fderiv ℝ (realChartChange a b) q.1 (chartGeodesicAcceleration h a q.1 q.2) +
      fderiv ℝ (fderiv ℝ (realChartChange a b)) q.1 q.2 q.2) =
    (fderiv ℝ (realChartChange a b) q.1 q.2,
      chartGeodesicAcceleration h b (realChartChange a b q.1) (fderiv ℝ (realChartChange a b) q.1 q.2))
  apply Prod.ext
  · rfl
  · rw [chartGeodesicAcceleration_eq, chartGeodesicAcceleration_eq, map_neg,
      chartChristoffelBilin_change h hh a b hq hy q.2 q.2]
    abel

theorem realTangentEnergy_contMDiff (h : HermitianField M) (hh : MetricSmooth h) :
    letI := manifold_realSmooth M
    ContMDiff (realPhaseModel n) 𝓘(ℝ, ℝ) ∞ (realTangentEnergy h) := by
  letI := manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup h y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace h y
  letI := realRiemannianBundle_contMDiff h hh
  have hv : ContMDiff (realPhaseModel n) (realPhaseModel n) ∞
      (fun q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier => q) := contMDiff_id
  have hs := ContMDiff.inner_bundle (IB := 𝓘(ℝ, ComplexVector n))
    (b := fun q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier => q.proj)
    (v := fun q => q.2) (w := fun q => q.2) hv hv
  exact hs

end Yau.LeafProofs.L23Aux

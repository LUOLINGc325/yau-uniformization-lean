import Yau.LeafProofs.L12

/-!
The genuine real Riemannian geometry of a smooth Hermitian field. No completeness
or Kähler condition is required by these constructions.
-/

noncomputable section
open MeasureTheory Filter Bundle
open scoped Topology Manifold ENNReal Matrix ContDiff
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem underlyingRealRiemannianMetric_frame_smooth
    (h : HermitianField M) (hh : MetricSmooth h)
    (x : M.Carrier) (a b : RIdx n) :
    ContDiffOn ℝ ∞ (fun z => (underlyingRealRiemannianMetric h).inner (chartInv x z)
      (realChartVec x z (realVec a)) (realChartVec x z (realVec b))) (chartTarget x) := by
  apply (hh x a b).congr
  intro z hz
  exact underlyingRealRiemannianMetric_frame h x z hz a b

theorem realMetricInChart_smooth (h : HermitianField M) (hh : MetricSmooth h) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (realMetricInChart h x) (chartTarget x) := by
  apply contDiffOn_realBilin_of_basis
  intro a b
  simpa only [realMetricInChart_apply] using
    underlyingRealRiemannianMetric_frame_smooth h hh x a b

open Bundle in
set_option maxHeartbeats 400000 in
def smoothUnderlyingRealRiemannianMetric (h : HermitianField M) (hh : MetricSmooth h) :
    letI := manifold_realSmooth M
    ContMDiffRiemannianMetric 𝓘(ℝ, ComplexVector n) ∞ (ComplexVector n)
      (fun x : M.Carrier => TangentSpace 𝓘(ℝ, ComplexVector n) x) := by
  letI := manifold_realSmooth M
  let G := underlyingRealRiemannianMetric h
  refine
    { inner := G.inner
      symm := G.symm
      pos := G.pos
      isVonNBounded := G.isVonNBounded
      contMDiff := ?_ }
  intro x
  rw [contMDiffAt_section]
  rw [contMDiffAt_iff_source]
  simp only [ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ,
    contMDiffAt_iff_contDiffAt]
  have hn : chartTarget x ∈ 𝓝 (chartPt x x) :=
    extChartAt_target_mem_nhds (I := ComplexModel n) x
  have hc := (realMetricInChart_smooth h hh x).contDiffAt hn
  have heq : ∀ z ∈ chartTarget x,
      (trivializationAt (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ)
        (fun y : M.Carrier => TangentSpace 𝓘(ℝ, ComplexVector n) y →L[ℝ]
          TangentSpace 𝓘(ℝ, ComplexVector n) y →L[ℝ] ℝ) x
        ⟨chartInv x z, G.inner (chartInv x z)⟩).2 = realMetricInChart h x z := by
    intro z hz
    have hy : chartInv x z ∈ (chartAt (ComplexVector n) x).source := by
      simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) x).map_target hz
    have hbase : chartInv x z ∈ (trivializationAt (ComplexVector n)
        (fun y : M.Carrier => TangentSpace 𝓘(ℝ, ComplexVector n) y) x).baseSet := hy
    have hframe : ∀ u : ComplexVector n,
        (trivializationAt (ComplexVector n)
          (fun y : M.Carrier => TangentSpace 𝓘(ℝ, ComplexVector n) y) x).symm
            (chartInv x z) u = realChartVec x z u := by
      intro u
      rw [← (trivializationAt (ComplexVector n)
        (fun y : M.Carrier => TangentSpace 𝓘(ℝ, ComplexVector n) y) x).symmL_apply (R := ℝ) hbase u]
      rw [TangentBundle.symmL_trivializationAt (I := 𝓘(ℝ, ComplexVector n)) hy]
      simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ]
      change mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) (chartInv x)
        (chartPt x (chartInv x z))
        ((tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) (chartPt x (chartInv x z))).symm u) = _
      have hpt : chartPt x (chartInv x z) = z := (extChartAt (ComplexModel n) x).right_inv hz
      rw [hpt]
      rfl
    ext u v
    simp only [hom_trivializationAt_apply]
    rw [inCoordinates_apply_eq₂ hbase hbase (Set.mem_univ _)]
    simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
      LinearMap.id_coe, id_eq]
    rw [realMetricInChart_apply, hframe, hframe]
  apply hc.congr_of_eventuallyEq
  filter_upwards [hn] with z hz
  exact heq z hz


theorem smoothUnderlyingRealRiemannianMetric_toRiemannianMetric (h : HermitianField M) (hh : MetricSmooth h) :
    letI := manifold_realSmooth M
    (smoothUnderlyingRealRiemannianMetric h hh).toRiemannianMetric =
      underlyingRealRiemannianMetric h := by
  rfl


theorem realRiemannianBundle_continuous (h : HermitianField M) (hh : MetricSmooth h) :
    letI := manifold_realSmooth M
    letI : ∀ x : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
      fun x => underlyingRealTangentNormedAddCommGroup h x
    letI : ∀ x : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
      fun x => underlyingRealTangentInnerProductSpace h x
    IsContinuousRiemannianBundle (ComplexVector n)
      (fun x : M.Carrier => TangentSpace 𝓘(ℝ, ComplexVector n) x) := by
  letI := manifold_realSmooth M
  letI : ∀ x : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
    fun x => underlyingRealTangentNormedAddCommGroup h x
  letI : ∀ x : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
    fun x => underlyingRealTangentInnerProductSpace h x
  refine ⟨(underlyingRealRiemannianMetric h).inner, ?_, ?_⟩
  · exact (smoothUnderlyingRealRiemannianMetric h hh).contMDiff.continuous
  · intro x v w
    rfl

theorem realRiemannianBundle_contMDiff (h : HermitianField M) (hh : MetricSmooth h) :
    letI := manifold_realSmooth M
    letI : ∀ x : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
      fun x => underlyingRealTangentNormedAddCommGroup h x
    letI : ∀ x : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
      fun x => underlyingRealTangentInnerProductSpace h x
    IsContMDiffRiemannianBundle 𝓘(ℝ, ComplexVector n) ∞ (ComplexVector n)
      (fun x : M.Carrier => TangentSpace 𝓘(ℝ, ComplexVector n) x) := by
  letI := manifold_realSmooth M
  letI : ∀ x : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
    fun x => underlyingRealTangentNormedAddCommGroup h x
  letI : ∀ x : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
    fun x => underlyingRealTangentInnerProductSpace h x
  refine ⟨(underlyingRealRiemannianMetric h).inner, ?_, ?_⟩
  · exact (smoothUnderlyingRealRiemannianMetric h hh).contMDiff
  · intro x v w
    rfl


theorem continuous_norm_realCurveVelocity (h : HermitianField M) (hh : MetricSmooth h) {f : ℝ → M.Carrier}
    (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 f) :
    letI : ∀ x : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
      fun x => underlyingRealTangentNormedAddCommGroup h x
    Continuous (fun t => ‖realCurveVelocity f t‖) := by
  letI := manifold_realSmooth M
  letI : ∀ x : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
    fun x => underlyingRealTangentNormedAddCommGroup h x
  letI : ∀ x : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
    fun x => underlyingRealTangentInnerProductSpace h x
  letI := realRiemannianBundle_continuous h hh
  have hv := continuous_realCurveVelocity hf
  have hi := hv.inner_bundle hv
  have hs := Real.continuous_sqrt.comp hi
  convert! hs using 1



theorem integrable_curveSpeed_of_contMDiff (h : HermitianField M) (hh : MetricSmooth h) {f : ℝ → M.Carrier}
    (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 f) :
    IntegrableOn (curveSpeed h (piecewiseC1Curve_of_contMDiff hf)) (Set.Icc (0 : ℝ) 1) := by
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup h z
  have hc : Continuous (curveSpeed h (piecewiseC1Curve_of_contMDiff hf)) := by
    convert! continuous_norm_realCurveVelocity h hh hf using 1
    ext t
    rw [underlyingRealTangent_norm,
      realCurveVelocity_chart hf.continuous.continuousAt
        ((contDiffAt_chart_of_contMDiff hf t).differentiableAt (by norm_num))]
    unfold curveSpeed
    rw [realTangentDerivative_eq_chart]
    rfl
  exact hc.continuousOn.integrableOn_compact isCompact_Icc

def integrableCurve_of_contMDiff (h : HermitianField M) (hh : MetricSmooth h) {f : ℝ → M.Carrier}
    (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 f) :
    IntegrableCurve h (f 0) (f 1) :=
  ⟨piecewiseC1Curve_of_contMDiff hf, integrable_curveSpeed_of_contMDiff h hh hf⟩

theorem inducedDistance_le_riemannianEDist (h : HermitianField M) (hh : MetricSmooth h) (x y : M.Carrier) :
    letI := manifold_realSmooth M
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup h z
    ENNReal.ofReal (inducedDistance h x y) ≤
      Manifold.riemannianEDist 𝓘(ℝ, ComplexVector n) x y := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup h z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace h z
  by_contra! hr
  obtain ⟨f, hx, hy, hf, hlen, _, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hr zero_lt_one
  let γ := integrableCurve_of_contMDiff h hh hf
  have hD := inducedDistance_le_curveLength h γ
  have hD' : inducedDistance h x y ≤ curveLength h γ.1 :=
    (congrArg₂ (inducedDistance h) hx hy).ge.trans hD
  have hLen := curveLength_eq_pathELength h γ
  change ENNReal.ofReal (curveLength h γ.1) =
    Manifold.pathELength 𝓘(ℝ, ComplexVector n) f 0 1 at hLen
  have hcontra : ENNReal.ofReal (inducedDistance h x y) ≤
      Manifold.pathELength 𝓘(ℝ, ComplexVector n) f 0 1 := by
    rw [← hLen]
    exact ENNReal.ofReal_le_ofReal hD'
  exact (not_lt_of_ge hcontra) hlen


@[instance_reducible]

def realEMetricSpace (h : HermitianField M) (hh : MetricSmooth h) : EMetricSpace M.Carrier := by
  letI := manifold_realSmooth M
  letI := manifold_locallyCompact M
  letI := realRiemannianBundle h
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup h z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace h z
  letI := realRiemannianBundle_continuous h hh
  exact EMetricSpace.ofRiemannianMetric 𝓘(ℝ, ComplexVector n) M.Carrier

set_option backward.isDefEq.respectTransparency false in
theorem realEMetricSpace_edist (h : HermitianField M) (hh : MetricSmooth h) (x y : M.Carrier) :
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup h z
    @edist M.Carrier (realEMetricSpace h hh).toEDist x y =
      Manifold.riemannianEDist 𝓘(ℝ, ComplexVector n) x y := by
  rfl

theorem realEMetricSpace_topology (h : HermitianField M) (hh : MetricSmooth h) :
    (realEMetricSpace h hh).toUniformSpace.toTopologicalSpace = M.topology := rfl


theorem riemannianEDist_le_pathELength_of_contMDiffAt_Ioo (h : HermitianField M) (hh : MetricSmooth h)
    {f : ℝ → M.Carrier} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Set.Icc a b))
    (hd : ∀ t ∈ Set.Ioo a b, ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 f t) :
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup h z
    Manifold.riemannianEDist 𝓘(ℝ, ComplexVector n) (f a) (f b) ≤
      Manifold.pathELength 𝓘(ℝ, ComplexVector n) f a b := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup h z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace h z
  letI := realEMetricSpace h hh
  rcases hab.eq_or_lt with rfl | hab
  · simp [Manifold.riemannianEDist_self]
  have hordered : ∀ u ∈ Set.Ioo a b, ∀ v ∈ Set.Ioo a b, u ≤ v →
      edist (f u) (f v) ≤ Manifold.pathELength 𝓘(ℝ, ComplexVector n) f a b := by
    intro u hu v hv huv
    rw [realEMetricSpace_edist h hh]
    apply (Manifold.riemannianEDist_le_pathELength (γ := f)
      (a := u) (b := v) (x := f u) (y := f v) ?_ rfl rfl huv).trans
        (Manifold.pathELength_mono hu.1.le hv.2.le)
    intro t ht
    exact (hd t ⟨hu.1.trans_le ht.1, ht.2.trans_lt hv.2⟩).contMDiffWithinAt
  have hbound : ∀ p ∈ Set.Ioo a b ×ˢ Set.Ioo a b,
      edist (f p.1) (f p.2) ≤ Manifold.pathELength 𝓘(ℝ, ComplexVector n) f a b := by
    intro p hp
    rcases le_total p.1 p.2 with h | h
    · exact hordered _ hp.1 _ hp.2 h
    · rw [edist_comm]
      exact hordered _ hp.2 _ hp.1 h
  have hcl : closure (Set.Ioo a b ×ˢ Set.Ioo a b) = Set.Icc a b ×ˢ Set.Icc a b := by
    rw [closure_prod_eq, closure_Ioo hab.ne]
  have hfst : ContinuousOn (fun p : ℝ × ℝ => f p.1) (Set.Icc a b ×ˢ Set.Icc a b) :=
    hc.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have hsnd : ContinuousOn (fun p : ℝ × ℝ => f p.2) (Set.Icc a b ×ˢ Set.Icc a b) :=
    hc.comp continuous_snd.continuousOn (fun _ hp => hp.2)
  have hdist := continuous_edist.comp_continuousOn (hfst.prodMk hsnd)
  have hend := le_on_closure hbound (by rw [hcl]; convert! hdist using 1) continuousOn_const
    (x := (a, b)) (by rw [hcl]; exact ⟨⟨le_rfl, hab.le⟩, ⟨hab.le, le_rfl⟩⟩)
  rw [realEMetricSpace_edist h hh] at hend
  exact hend

theorem riemannianEDist_le_pathELength_of_finite_exceptions (h : HermitianField M) (hh : MetricSmooth h)
    {f : ℝ → M.Carrier} (s : Finset ℝ) {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Set.Icc a b))
    (hd : ∀ t ∈ Set.Ioo a b, t ∉ s →
      ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 f t) :
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup h z
    Manifold.riemannianEDist 𝓘(ℝ, ComplexVector n) (f a) (f b) ≤
      Manifold.pathELength 𝓘(ℝ, ComplexVector n) f a b := by
  classical
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup h z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace h z
  induction s using Finset.induction_on generalizing a b with
  | empty =>
    apply riemannianEDist_le_pathELength_of_contMDiffAt_Ioo h hh hab hc
    intro t ht
    exact hd t ht (by simp)
  | @insert c s hcs ih =>
    by_cases hac : a < c
    · by_cases hcb : c < b
      · have hleft := ih hac.le
          (hc.mono (Set.Icc_subset_Icc le_rfl hcb.le))
          (fun t ht hnot => hd t ⟨ht.1, ht.2.trans hcb⟩
            (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_lt ht.2, hnot⟩))
        have hright := ih hcb.le
          (hc.mono (Set.Icc_subset_Icc hac.le le_rfl))
          (fun t ht hnot => hd t ⟨hac.trans ht.1, ht.2⟩
            (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_gt ht.1, hnot⟩))
        exact (Manifold.riemannianEDist_triangle (I := 𝓘(ℝ, ComplexVector n))
          (x := f a) (y := f c) (z := f b)).trans
            ((add_le_add hleft hright).trans_eq (Manifold.pathELength_add hac.le hcb.le))
      · apply ih hab hc
        intro t ht hnot
        apply hd t ht
        simp only [Finset.mem_insert, not_or]
        exact ⟨ne_of_lt (ht.2.trans_le (le_of_not_gt hcb)), hnot⟩
    · apply ih hab hc
      intro t ht hnot
      apply hd t ht
      simp only [Finset.mem_insert, not_or]
      exact ⟨ne_of_gt ((le_of_not_gt hac).trans_lt ht.1), hnot⟩

theorem riemannianEDist_le_curveLength (h : HermitianField M) (hh : MetricSmooth h) {x y : M.Carrier}
    (γ : IntegrableCurve h x y) :
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup h z
    Manifold.riemannianEDist 𝓘(ℝ, ComplexVector n) x y ≤
      ENNReal.ofReal (curveLength h γ.1) := by
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup h z
  rw [curveLength_eq_pathELength h γ]
  have hd := riemannianEDist_le_pathELength_of_finite_exceptions h hh γ.1.breakpoints
    zero_le_one γ.1.continuous_on (fun t ht hnot => ?_)
  · simpa only [γ.1.start_eq, γ.1.finish_eq] using hd
  · rw [contMDiffAt_iff]
    refine ⟨γ.1.continuous_on.continuousAt (Icc_mem_nhds ht.1 ht.2), ?_⟩
    simp only [real_extChartAt_eq, mfld_simps, contDiffWithinAt_univ]
    convert! γ.1.piecewise_c1 t hnot using 1


def realLeviCivitaConnection (h : HermitianField M) (hh : MetricSmooth h) :
    letI := manifold_realSmooth M
    CovariantDerivative 𝓘(ℝ, ComplexVector n) (ComplexVector n)
      (TangentSpace 𝓘(ℝ, ComplexVector n) : M.Carrier → Type) := by
  letI := manifold_realSmooth M
  letI := realRiemannianBundle h
  letI := realRiemannianBundle_contMDiff h hh
  exact CovariantDerivative.leviCivitaConnection 𝓘(ℝ, ComplexVector n) M.Carrier

theorem realLeviCivitaConnection_isLeviCivita (h : HermitianField M) (hh : MetricSmooth h) :
    letI := manifold_realSmooth M
    letI := realRiemannianBundle h
    letI := realRiemannianBundle_contMDiff h hh
    CovariantDerivative.IsLeviCivitaConnection 𝓘(ℝ, ComplexVector n)
      (realLeviCivitaConnection h hh) := by
  letI := manifold_realSmooth M
  letI := realRiemannianBundle h
  letI := realRiemannianBundle_contMDiff h hh
  exact CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection 𝓘(ℝ, ComplexVector n)


/-- Finiteness of extended distances on a connected emetric space. -/
theorem connected_edist_ne_top {X : Type*} [EMetricSpace X] [ConnectedSpace X]
    (x y : X) : edist x y ≠ ⊤ := by
  let S : Set X := {z | edist x z < ⊤}
  have hopen : IsOpen S := isOpen_lt (continuous_const.edist continuous_id) continuous_const
  have hcopen : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    apply EMetric.mem_nhds_iff.mpr
    refine ⟨1, zero_lt_one, ?_⟩
    intro w hw
    change ¬ edist x w < ⊤
    intro hxw
    apply hz
    change edist x z < ⊤
    exact (edist_triangle x w z).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hxw, hw.trans (by simp)⟩)
  have hcl : IsClopen S := ⟨by simpa only [compl_compl] using hcopen.isClosed_compl, hopen⟩
  have hS : S = Set.univ := hcl.eq_univ ⟨x, by simp [S]⟩
  have hy : y ∈ S := hS.symm ▸ Set.mem_univ y
  exact hy.ne

theorem integrable_curve_nonempty (h : HermitianField M) (hh : MetricSmooth h)
    (x y : M.Carrier) : Nonempty (IntegrableCurve h x y) := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup h z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace h z
  letI := realEMetricSpace h hh
  have hfin : Manifold.riemannianEDist 𝓘(ℝ, ComplexVector n) x y < ⊤ :=
    lt_top_iff_ne_top.mpr (connected_edist_ne_top x y)
  obtain ⟨f, hx, hy, hf, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hfin zero_lt_one
  rw [← hx, ← hy]
  exact ⟨integrableCurve_of_contMDiff h hh hf⟩

theorem inducedDistance_nonneg (h : HermitianField M) (hh : MetricSmooth h)
    (x y : M.Carrier) : 0 ≤ inducedDistance h x y := by
  obtain ⟨γ⟩ := integrable_curve_nonempty h hh x y
  apply le_csInf ⟨_, Set.mem_range_self γ⟩
  rintro _ ⟨η, rfl⟩
  exact curveLength_nonneg h η.1

theorem exists_nearMinimizingCurve (h : HermitianField M) (hh : MetricSmooth h) (x y : M.Carrier)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : IntegrableCurve h x y,
      curveLength h γ.1 < inducedDistance h x y + ε := by
  obtain ⟨γ⟩ := integrable_curve_nonempty h hh x y
  have hne : (Set.range (fun η : IntegrableCurve h x y =>
      curveLength h η.1)).Nonempty := ⟨_, Set.mem_range_self γ⟩
  have hlt : sInf (Set.range (fun η : IntegrableCurve h x y =>
      curveLength h η.1)) < inducedDistance h x y + ε := by
    exact lt_add_of_pos_right _ hε
  obtain ⟨_, ⟨η, rfl⟩, hη⟩ := exists_lt_of_csInf_lt hne hlt
  exact ⟨η, hη⟩


theorem inducedDistance_eq_riemannianEDist (h : HermitianField M) (hh : MetricSmooth h) (x y : M.Carrier) :
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup h z
    ENNReal.ofReal (inducedDistance h x y) =
      Manifold.riemannianEDist 𝓘(ℝ, ComplexVector n) x y := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup h z
  apply le_antisymm (inducedDistance_le_riemannianEDist h hh x y)
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  by_cases hrinf : r = ⊤
  · exact hrinf ▸ le_top
  have hpos : 0 < r.toReal :=
    ENNReal.toReal_pos (lt_of_le_of_lt (zero_le : (0 : ℝ≥0∞) ≤ _) hr).ne' hrinf
  have hreal : inducedDistance h x y < r.toReal := by
    rw [← ENNReal.ofReal_toReal hrinf] at hr
    exact (ENNReal.ofReal_lt_ofReal_iff hpos).mp hr
  obtain ⟨γ, hγ⟩ := exists_nearMinimizingCurve h hh x y (sub_pos.mpr hreal)
  exact (riemannianEDist_le_curveLength h hh γ).trans
    ((ENNReal.ofReal_le_ofReal (show curveLength h γ.1 ≤ r.toReal by linarith)).trans_eq (ENNReal.ofReal_toReal hrinf))


/-- The project distance itself, with the original topology. -/
@[instance_reducible]
def metricSpaceOfField (h : HermitianField M) (hh : MetricSmooth h) : MetricSpace M.Carrier := by
  letI := realEMetricSpace h hh
  apply EMetricSpace.toMetricSpaceOfDist (inducedDistance h) (inducedDistance_nonneg h hh)
  intro x y
  exact (inducedDistance_eq_riemannianEDist h hh x y).symm

theorem metricSpaceOfField_dist (h : HermitianField M) (hh : MetricSmooth h)
    (x y : M.Carrier) :
    @dist M.Carrier (metricSpaceOfField h hh).toDist x y = inducedDistance h x y := rfl

theorem metricSpaceOfField_topology (h : HermitianField M) (hh : MetricSmooth h) :
    (metricSpaceOfField h hh).toUniformSpace.toTopologicalSpace = M.topology := rfl


theorem inducedDistance_self (h : HermitianField M) (hh : MetricSmooth h) (x : M.Carrier) :
    inducedDistance h x x = 0 := by
  letI := metricSpaceOfField h hh
  exact dist_self x

theorem inducedDistance_symm (h : HermitianField M) (hh : MetricSmooth h) (x y : M.Carrier) :
    inducedDistance h x y = inducedDistance h y x := by
  letI := metricSpaceOfField h hh
  exact dist_comm x y

theorem inducedDistance_triangle (h : HermitianField M) (hh : MetricSmooth h)
    (x y z : M.Carrier) :
    inducedDistance h x z ≤ inducedDistance h x y + inducedDistance h y z := by
  letI := metricSpaceOfField h hh
  exact dist_triangle x y z

theorem continuous_inducedDistance (h : HermitianField M) (hh : MetricSmooth h) :
    Continuous (fun q : M.Carrier × M.Carrier => inducedDistance h q.1 q.2) := by
  letI := metricSpaceOfField h hh
  exact continuous_dist

theorem continuous_distFrom (h : HermitianField M) (hh : MetricSmooth h) (x : M.Carrier) :
    Continuous (inducedDistance h x) := by
  letI := metricSpaceOfField h hh
  exact continuous_const.dist continuous_id

theorem mem_distBall_iff (h : HermitianField M) (x y : M.Carrier) {r : ℝ} (hr : 0 < r) :
    y ∈ distBall h x r ↔ inducedDistance h x y < r :=
  ENNReal.ofReal_lt_ofReal_iff hr

theorem distBall_eq_metric_ball (h : HermitianField M) (hh : MetricSmooth h)
    (x : M.Carrier) {r : ℝ} (hr : 0 < r) :
    distBall h x r = @Metric.ball M.Carrier (metricSpaceOfField h hh).toPseudoMetricSpace x r := by
  ext y
  rw [mem_distBall_iff h x y hr]
  change inducedDistance h x y < r ↔ inducedDistance h y x < r
  rw [inducedDistance_symm h hh x y]

theorem isOpen_distBall (h : HermitianField M) (hh : MetricSmooth h)
    (x : M.Carrier) (r : ℝ) : IsOpen (distBall h x r) := by
  by_cases hr : 0 < r
  · letI := metricSpaceOfField h hh
    rw [distBall_eq_metric_ball h hh x hr]
    exact Metric.isOpen_ball
  · rw [L12Aux.distBall_eq_empty_of_nonpos h x (le_of_not_gt hr)]
    exact isOpen_empty

end Yau.LeafProofs.L23Aux

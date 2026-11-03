import Yau.Proofs.P07DistanceLeviConnection
import Yau.LeafProofs.L23FieldMetricParallelVariation

noncomputable section
open Filter
open scoped Topology ContDiff Manifold NNReal

namespace Yau.NodeProofs.P07DistanceLevi
open Yau Yau.LeafProofs L12Aux L23Aux L23LocalDistanceContract

/-- Local uniqueness for the genuine time dependent linear parallel ODE. -/
theorem linearODE_eventuallyEq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : ℝ → E →L[ℝ] E} {f g : ℝ → E} {t : ℝ}
    (hA : ContinuousAt A t)
    (hf : ∀ᶠ s in 𝓝 t, HasDerivAt f (A s (f s)) s)
    (hg : ∀ᶠ s in 𝓝 t, HasDerivAt g (A s (g s)) s)
    (heq : f t = g t) : f =ᶠ[𝓝 t] g := by
  let K : ℝ≥0 := ⟨‖A t‖ + 1, by positivity⟩
  have hbound : ∀ᶠ s in 𝓝 t, ‖A s‖ ≤ (K : ℝ) :=
    (hA.norm.eventually (gt_mem_nhds (lt_add_one ‖A t‖))).mono fun _ h => h.le
  apply ODE_solution_unique_of_eventually (v := fun s x => A s x)
    (s := fun _ => Set.univ) (K := K) ?_ ?_ ?_ heq
  · filter_upwards [hbound] with s hs
    exact ((A s).lipschitzWith.weaken (show ‖A s‖₊ ≤ K from hs)).lipschitzOnWith
  · exact hf.mono fun s hs => ⟨hs, Set.mem_univ _⟩
  · exact hg.mono fun s hs => ⟨hs, Set.mem_univ _⟩

variable {n : ℕ} {M : ComplexManifold n}

theorem realTangentCoords_change (a b y : M.Carrier)
    (ha : y ∈ (chartAt (ComplexVector n) a).source)
    (hb : y ∈ (chartAt (ComplexVector n) b).source)
    (V : TangentSpace 𝓘(ℝ, ComplexVector n) y) :
    realTangentCoords b y V =
      fderiv ℝ (realChartChange a b) (chartPt a y) (realTangentCoords a y V) := by
  have H := congrArg (fun L => L (realTangentCoords a y V))
    (realTangentCoords_comp_realFrameCLM_change a b y ha hb)
  simpa only [ContinuousLinearMap.comp_apply, realFrameCLM_realTangentCoords a y ha] using H

theorem realChartChange_fderiv_I (a b : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a)
    (hb : chartInv a z ∈ (extChartAt (ComplexModel n) b).source) (v : ComplexVector n) :
    fderiv ℝ (realChartChange a b) z (Complex.I • v) =
      Complex.I • fderiv ℝ (realChartChange a b) z v := by
  have hD := (chartTransition_contDiffAt a b hz hb).differentiableAt (by simp)
  have hreal (w : ComplexVector n) :
      fderiv ℝ (realChartChange a b) z w =
        fderiv ℂ (realChartChange a b) z w := by
    exact congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => L w)
      (hD.fderiv_restrictScalars ℝ)
  rw [hreal, hreal, map_smul]

/-- Complex-linearity of a tangent map is independent of the containing chart. -/
theorem parallel_I_coordinates_change (a b y : M.Carrier)
    (ha : y ∈ (chartAt (ComplexVector n) a).source)
    (hb : y ∈ (chartAt (ComplexVector n) b).source)
    (U V : TangentSpace 𝓘(ℝ, ComplexVector n) y)
    (hUV : realTangentCoords a y U = Complex.I • realTangentCoords a y V) :
    realTangentCoords b y U = Complex.I • realTangentCoords b y V := by
  have hz : chartPt a y ∈ chartTarget a :=
    (extChartAt (ComplexModel n) a).map_source (by simpa only [extChartAt_source] using ha)
  have hi : chartInv a (chartPt a y) = y :=
    (extChartAt (ComplexModel n) a).left_inv (by simpa only [extChartAt_source] using ha)
  have hbs : chartInv a (chartPt a y) ∈ (extChartAt (ComplexModel n) b).source := by
    simpa only [hi, extChartAt_source] using hb
  rw [realTangentCoords_change a b y ha hb U,
    realTangentCoords_change a b y ha hb V, hUV, realChartChange_fderiv_I a b hz hbs]

/-- Both parallel fields solve the same actual linear ODE in a fixed
chart, so agreement with `I` at one time persists near that time. -/
theorem parallel_coordinates_eventually_I
    (h : HermitianField M) (hh : MetricSmooth h) (hk : KahlerClosed h)
    (γ : ℝ → M.Carrier)
    (P : (s : ℝ) → ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ s))
    (a b : ℝ) (c : M.Carrier) (t : ℝ) (ht : t ∈ Set.Ioo a b)
    (hc : γ t ∈ (chartAt (ComplexVector n) c).source)
    (hP : ∀ (d : M.Carrier) (s : ℝ), s ∈ Set.Ioo a b →
      γ s ∈ (chartAt (ComplexVector n) d).source → ∀ w : ComplexVector n,
      HasDerivAt (fun r => realTangentCoords d (γ r) (P r w))
        (-chartChristoffelBilin h d (chartPt d (γ s)) (geoChartState γ d s).2
          (realTangentCoords d (γ s) (P s w))) s)
    (v : ComplexVector n)
    (heq : realTangentCoords c (γ t) (P t (Complex.I • v)) =
      Complex.I • realTangentCoords c (γ t) (P t v)) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 γ (Set.Ioo a b) →
    (fun s => realTangentCoords c (γ s) (P s (Complex.I • v))) =ᶠ[𝓝 t]
      (fun s => Complex.I • realTangentCoords c (γ s) (P s v)) := by
  letI := manifold_realSmooth M
  intro hγ
  let K := Set.Ioo a b ∩ γ ⁻¹' (chartAt (ComplexVector n) c).source
  have hK : IsOpen K := hγ.continuousOn.isOpen_inter_preimage isOpen_Ioo
    (chartAt (ComplexVector n) c).open_source
  have htK : t ∈ K := ⟨ht,hc⟩
  have hA := chartParallelCoefficient_contDiffOn_two h hh γ c K hK
    (hγ.mono (fun s hs => hs.1)) (fun s hs => hs.2)
  apply linearODE_eventuallyEq (hA.continuousOn.continuousAt (hK.mem_nhds htK)) ?_ ?_ heq
  · filter_upwards [hK.mem_nhds htK] with s hs
    exact hP c s hs.1 hs.2 (Complex.I • v)
  · filter_upwards [hK.mem_nhds htK] with s hs
    have H := (L12Aux.complexStructureCLM n).hasFDerivAt.comp_hasDerivAt s
      (hP c s hs.1 hs.2 v)
    have hz : chartPt c (γ s) ∈ chartTarget c :=
      (extChartAt (ComplexModel n) c).map_source (by simpa only [Set.mem_preimage, extChartAt_source] using hs.2)
    change HasDerivAt (fun r => Complex.I • realTangentCoords c (γ r) (P r v))
      (Complex.I • (-chartChristoffelBilin h c (chartPt c (γ s))
        (geoChartState γ c s).2 (realTangentCoords c (γ s) (P s v)))) s at H
    simpa only [chartParallelCoefficient, geoChartState, ContinuousLinearMap.neg_apply,
      smul_neg, chartChristoffelBilin_I_right h hh hk c hz] using H

/-- Uniqueness propagates over the connected time interval. In particular,
the actual endpoint parallel transport commutes with `I` in every chart. -/
theorem parallel_coordinates_I
    (h : HermitianField M) (hh : MetricSmooth h) (hk : KahlerClosed h)
    (γ : ℝ → M.Carrier)
    (P : (s : ℝ) → ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ s))
    (a b t₀ : ℝ) (ht₀ : t₀ ∈ Set.Ioo a b)
    (hP : ∀ (d : M.Carrier) (s : ℝ), s ∈ Set.Ioo a b →
      γ s ∈ (chartAt (ComplexVector n) d).source → ∀ w : ComplexVector n,
      HasDerivAt (fun r => realTangentCoords d (γ r) (P r w))
        (-chartChristoffelBilin h d (chartPt d (γ s)) (geoChartState γ d s).2
          (realTangentCoords d (γ s) (P s w))) s)
    (v : ComplexVector n)
    (hinit : realTangentCoords (γ t₀) (γ t₀) (P t₀ (Complex.I • v)) =
      Complex.I • realTangentCoords (γ t₀) (γ t₀) (P t₀ v)) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 γ (Set.Ioo a b) →
    ∀ t ∈ Set.Ioo a b, ∀ c : M.Carrier,
      γ t ∈ (chartAt (ComplexVector n) c).source →
      realTangentCoords c (γ t) (P t (Complex.I • v)) =
        Complex.I • realTangentCoords c (γ t) (P t v) := by
  letI := manifold_realSmooth M
  intro hγ
  let I := Set.Ioo a b
  letI : PreconnectedSpace I := Subtype.preconnectedSpace (convex_Ioo a b).isPreconnected
  let V : Set I := {t | ∀ c : M.Carrier,
    γ t.val ∈ (chartAt (ComplexVector n) c).source →
    realTangentCoords c (γ t.val) (P t.val (Complex.I • v)) =
      Complex.I • realTangentCoords c (γ t.val) (P t.val v)}
  have hclosed : IsClosed V := by
    apply isClosed_iff_frequently.mpr
    intro t ht
    let c := γ t.val
    have hc : γ t.val ∈ (chartAt (ComplexVector n) c).source := mem_chart_source _ _
    have hsrc : ∀ᶠ s : I in 𝓝 t, γ s.val ∈ (chartAt (ComplexVector n) c).source :=
      (hγ.continuousOn.restrict.continuousAt).preimage_mem_nhds
        ((chartAt (ComplexVector n) c).open_source.mem_nhds hc)
    have h₁ := (hP c t.val t.property hc (Complex.I • v)).continuousAt.comp continuousAt_subtype_val
    have h₂ := ((L12Aux.complexStructureCLM n).continuous.continuousAt.comp
      (hP c t.val t.property hc v).continuousAt).comp continuousAt_subtype_val
    have H : realTangentCoords c (γ t.val) (P t.val (Complex.I • v)) =
        Complex.I • realTangentCoords c (γ t.val) (P t.val v) := by
      apply tendsto_nhds_unique_of_frequently_eq h₁ h₂
      exact (ht.and_eventually hsrc).mono fun s hs => hs.1 c hs.2
    intro d hd
    exact parallel_I_coordinates_change c d (γ t.val) hc hd _ _ H
  have hopen : IsOpen V := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    let c := γ t.val
    have hc : γ t.val ∈ (chartAt (ComplexVector n) c).source := mem_chart_source _ _
    have H := parallel_coordinates_eventually_I h hh hk γ P a b c t.val t.property hc
      hP v (ht c hc) hγ
    have hsrc : ∀ᶠ s in 𝓝 t.val, γ s ∈ (chartAt (ComplexVector n) c).source :=
      (hγ.continuousOn.continuousAt (isOpen_Ioo.mem_nhds t.property)).preimage_mem_nhds
        ((chartAt (ComplexVector n) c).open_source.mem_nhds hc)
    have HV : ∀ᶠ s in 𝓝 t.val, ∀ d : M.Carrier,
        γ s ∈ (chartAt (ComplexVector n) d).source →
        realTangentCoords d (γ s) (P s (Complex.I • v)) =
          Complex.I • realTangentCoords d (γ s) (P s v) := by
      filter_upwards [H,hsrc] with s hs hsc
      intro d hd
      exact parallel_I_coordinates_change c d (γ s) hsc hd _ _ hs
    exact continuousAt_subtype_val.eventually HV
  have hV : V = Set.univ := IsClopen.eq_univ ⟨hclosed,hopen⟩ (by
    refine ⟨⟨t₀,ht₀⟩,?_⟩
    intro c hc
    exact parallel_I_coordinates_change (γ t₀) c (γ t₀) (mem_chart_source _ _) hc _ _ hinit)
  intro t ht c hc
  have H : (⟨t,ht⟩ : I) ∈ V := by rw [hV]; exact Set.mem_univ _
  exact H c hc

/-- The concrete parallel endpoint variation has the required terminal
condition, so its actual transported fields commute with `I`. -/
theorem parallelEndpoint_coordinates_I
    (h : HermitianField M) (hh : MetricSmooth h) (hk : KahlerClosed h)
    (γ : ℝ → M.Carrier)
    (P : (s : ℝ) → ComplexVector n ≃L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ s))
    (δ : ℝ) (hδ : 0 < δ)
    (hγ : FieldGeodesicOn h γ (Set.Ioo (-δ) (1+δ)))
    (hP1 : (P 1).toContinuousLinearMap = realFrameCLM (γ 1) (γ 1))
    (hP : ∀ (d : M.Carrier) (s : ℝ), s ∈ Set.Ioo (-δ) (1+δ) →
      γ s ∈ (chartAt (ComplexVector n) d).source → ∀ w : ComplexVector n,
      HasDerivAt (fun r => realTangentCoords d (γ r) (P r w))
        (-chartChristoffelBilin h d (chartPt d (γ s)) (geoChartState γ d s).2
          (realTangentCoords d (γ s) (P s w))) s)
    (v : ComplexVector n) :
    ∀ t ∈ Set.Ioo (-δ) (1+δ), ∀ c : M.Carrier,
      γ t ∈ (chartAt (ComplexVector n) c).source →
      realTangentCoords c (γ t) (P t (Complex.I • v)) =
        Complex.I • realTangentCoords c (γ t) (P t v) := by
  have h1 : (1 : ℝ) ∈ Set.Ioo (-δ) (1+δ) := by constructor <;> linarith
  have hinit : realTangentCoords (γ 1) (γ 1) ((P 1).toContinuousLinearMap (Complex.I • v)) =
      Complex.I • realTangentCoords (γ 1) (γ 1) ((P 1).toContinuousLinearMap v) := by
    rw [hP1,realTangentCoords_realFrameCLM _ _ (mem_chart_source _ _),
      realTangentCoords_realFrameCLM _ _ (mem_chart_source _ _)]
  exact parallel_coordinates_I h hh hk γ (fun s => (P s).toContinuousLinearMap)
    (-δ) (1+δ) 1 h1 hP v hinit hγ.1

end Yau.NodeProofs.P07DistanceLevi

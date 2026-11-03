import Yau.Proofs.C04RescaledTubeCurvatureScaling

/-! The original complex flow yields the actual real rescaled Ricci flow
with sigma one on every positive physical-time cylinder. -/
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter
namespace Yau.Proofs.C04RescaledTubeAux
open Yau Blueprint LeafProofs C04Aux NodeProofs
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem rescaled_metricFamilySmooth (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (ti R : ℝ) (hR : 0 < R) (I : Set ℝ)
    (htime : ∀ z ∈ I, 0 ≤ ti + z / R) :
    MetricFamilySmooth (fun z => scaleField R hR (h (ti + z / R))) I := by
  intro x a b
  simp only [realMetricFn_scale, Matrix.smul_apply, smul_eq_mul]
  have hmap : ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => (p.1, ti + p.2 / R))
      (chartTarget x ×ˢ I) :=
    contDiffOn_fst.prodMk (contDiffOn_const.add (contDiffOn_snd.div_const R))
  exact contDiffOn_const.mul ((hf.1.2.1 x a b).comp hmap
    (fun p hp => ⟨hp.1, htime p.2 hp.2⟩))

theorem rescaled_local_real_flow (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (ti R : ℝ) (hR : 0 < R) (O : Set (Pt X)) (I : Set ℝ)
    (htime : ∀ z ∈ I, 0 < ti + z / R) :
    LocalRealRicciFlow (fun z => scaleField R hR (h (ti + z / R))) O I 1 := by
  refine ⟨rescaled_metricFamilySmooth X o h U P ρ hf ti R hR I
    (fun z hz => (htime z hz).le), ?_⟩
  intro x hx z hz a b
  have ht := htime z hz
  have hflow := G04Aux.flowReal n X.manifold X.metric.form h hf.1
  have hd := (hflow.2 x (Set.mem_univ x) (ti + z / R) ht.le a b).hasDerivAt
    (Ici_mem_nhds ht)
  have htimeD := ((hasDerivAt_id z).div_const R).const_add ti
  have hcomp := (hd.comp z htimeD).const_mul R
  simp only [realMetricFn_scale, Matrix.smul_apply, smul_eq_mul]
  rw [realRicciCoeff_scale R hR _
    (localizedFlow_metricSmooth X o h U P ρ hf ht.le) x
    (z := chartPt x x) (mem_extChartAt_target x)]
  have hcancel (u : ℝ) : R * (-1 * u * (1 / R)) = -1 * u := by
    field_simp [hR.ne']
  simpa only [Function.comp_def, id_eq, hcancel] using hcomp.hasDerivWithinAt (s := I)

end Yau.Proofs.C04RescaledTubeAux

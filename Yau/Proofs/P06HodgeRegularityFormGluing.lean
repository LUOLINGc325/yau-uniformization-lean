import Yau.Proofs.P06HodgeRegularityPushforwardTime

/-! Actual dependent-form gluing. Smooth local representatives agree
pointwise on overlaps by full support of the original Riemannian volume. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

theorem regularitySmoothForm_eqOn_of_ae
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A B : RealForm M k) (hA : SmoothRealForm A) (hB : SmoothRealForm B)
    {O : Set M.Carrier} (hO : IsOpen O) (hAE : ∀ᵐ y ∂μ.restrict O, A y = B y) :
    ∀ y ∈ O, A y = B y := by
  letI : μ.IsOpenPosMeasure := L18Aux.riemannianVolume_isOpenPosMeasure g μ hμ
  have hD : SmoothRealForm (A-B) := (smoothFormSubmodule (M := M) k).sub_mem hA hB
  have hn : formNormSq g.form (A-B) =ᵐ[μ.restrict O] (fun _ => (0 : ℝ)) := by
    filter_upwards [hAE] with y hy
    exact (formNormSq_eq_zero_iff g.form (A-B) y).mpr (sub_eq_zero.mpr hy)
  intro y hy
  have hz := Measure.eqOn_open_of_ae_eq hn hO
    (formNormSq_continuous g (A-B) hD).continuousOn continuousOn_const hy
  exact sub_eq_zero.mp ((formNormSq_eq_zero_iff g.form (A-B) y).mp hz)

theorem regularityLocalForms_glue
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : ℝ → RealForm M k) (N : M.Carrier → Set M.Carrier)
    (hN : ∀ x, IsOpen (N x)) (hNx : ∀ x, x ∈ N x)
    (B : M.Carrier → ℝ → RealForm M k)
    (hB : ∀ x t, 0 < t → SmoothRealForm (B x t))
    (hBAE : ∀ x t, 0 < t → ∀ᵐ y ∂μ.restrict (N x), B x t y = A t y)
    (hBtime : ∀ x b (I : Fin k → RIdx n) z, z ∈ chartTarget b → ∀ t, 0 < t →
      chartInv b z ∈ N x → ContDiffAt ℝ ∞
        (fun p : ComplexVector n × ℝ => formComponents (B x p.2) b p.1 I) (z,t)) :
    ∃ U : ℝ → RealForm M k, SmoothFormTime U (Set.Ioi 0) ∧
      (∀ t, 0 < t → ∀ᵐ y ∂μ, U t y = A t y) ∧
      ∀ x t, 0 < t → ∀ y ∈ N x, U t y = B x t y := by
  let U : ℝ → RealForm M k := fun t y => B y t y
  have hlocal (x : M.Carrier) (t : ℝ) (ht : 0 < t) (y : M.Carrier) (hy : y ∈ N x) :
      U t y = B x t y := by
    have hAE : ∀ᵐ z ∂μ.restrict (N y ∩ N x), B y t z = B x t z := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left (hBAE y t ht),
        ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right (hBAE x t ht)] with z hz hyz
      exact hz.trans hyz.symm
    exact regularitySmoothForm_eqOn_of_ae g μ hμ (B y t) (B x t) (hB y t ht) (hB x t ht)
      ((hN y).inter (hN x)) hAE y ⟨hNx y,hy⟩
  refine ⟨U,?_,?_,hlocal⟩
  · intro b I p hp
    rcases p with ⟨z,t⟩
    have hz : z ∈ chartTarget b := hp.1
    have ht : 0 < t := hp.2
    let y := chartInv b z
    have hAt := hBtime y b I z hz t ht (hNx y)
    apply ContDiffAt.contDiffWithinAt
    apply hAt.congr_of_eventuallyEq
    have hi : ContinuousAt (chartInv b) z := by
      with_unfolding_all
        exact continuousAt_extChartAt_symm'' (I := ComplexModel n) hz
    have hspace : ∀ᶠ p : ComplexVector n × ℝ in 𝓝 (z,t), chartInv b p.1 ∈ N y :=
      (hi.tendsto.comp (continuous_fst.tendsto (z,t))).eventually ((hN y).mem_nhds (hNx y))
    have htime : ∀ᶠ p : ComplexVector n × ℝ in 𝓝 (z,t), 0 < p.2 :=
      continuous_snd.continuousAt.tendsto.eventually (Ioi_mem_nhds ht)
    filter_upwards [hspace,htime] with p hpy hpt
    change U p.2 (chartInv b p.1) (fun r => chartVec b (chartInv b p.1) (realVec (I r))) = _
    rw [hlocal y p.2 hpt (chartInv b p.1) hpy]
    rfl
  · intro t ht
    obtain ⟨cover,hcover⟩ := isLindelof_univ.indexed_countable_subcover N hN
      (fun y _ => Set.mem_iUnion.mpr ⟨y,hNx y⟩)
    have hEach (j : ℕ) : ∀ᵐ y ∂μ, y ∈ N (cover j) → U t y = A t y := by
      apply (ae_restrict_iff' (hN (cover j)).measurableSet).mp
      filter_upwards [ae_restrict_mem (hN (cover j)).measurableSet,hBAE (cover j) t ht] with y hy hya
      exact (hlocal (cover j) t ht y hy).trans hya
    filter_upwards [ae_all_iff.mpr hEach] with y hy
    obtain ⟨j,hjy⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ y))
    exact hy j hjy

end Yau.NodeProofs.P06Aux

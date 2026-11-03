import Yau.LeafProofs.L23FieldMetricSpray
import Yau.LeafProofs.L12ODEVariation

/-! Finite order joint local flow regularity from the actual tangent lift. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
universe u
set_option maxHeartbeats 1000000

def LocalODEFlowOrder (k : ℕ) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (F : E → E) (U : Set E) (z₀ : E),
    ContDiffOn ℝ ∞ F U → IsOpen U → z₀ ∈ U →
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ φ : E → ℝ → E,
      ∃ V : E → ℝ → E →L[ℝ] E,
      ContDiffOn ℝ k (Function.uncurry φ) (Metric.ball z₀ r ×ˢ Set.Ioo (-ε) ε) ∧
      ContinuousOn (Function.uncurry V) (Metric.ball z₀ r ×ˢ Set.Ioo (-ε) ε) ∧
      (∀ z ∈ Metric.ball z₀ r, φ z 0 = z ∧ V z 0 = ContinuousLinearMap.id ℝ E) ∧
      (∀ z ∈ Metric.ball z₀ r, ∀ t ∈ Set.Ioo (-ε) ε,
        φ z t ∈ U ∧ HasDerivAt (φ z) (F (φ z t)) t ∧
          HasDerivAt (V z) ((fderiv ℝ F (φ z t)).comp (V z t)) t) ∧
      (∀ p ∈ Metric.ball z₀ r ×ˢ Set.Ioo (-ε) ε,
        HasFDerivAt (fun z => φ z p.2) (V p.1 p.2) p.1) ∧
      (∀ p ∈ Metric.ball z₀ r ×ˢ Set.Ioo (-ε) ε,
        HasFDerivAt (Function.uncurry φ)
          ((V p.1 p.2).coprod (ContinuousLinearMap.toSpanSingleton ℝ (F (φ p.1 p.2)))) p)

theorem odeVariationField_contDiffAt_infty
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → E} {z : E} (hF : ContDiffAt ℝ ∞ F z) (A : E →L[ℝ] E) :
    ContDiffAt ℝ ∞ (odeVariationField F) (z,A) := by
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ F) z := hF.fderiv_right (by simp)
  exact (hF.comp _ contDiffAt_fst).prodMk
    ((hD.comp _ contDiffAt_fst).clm_comp contDiffAt_snd)

theorem localODEFlowOrder (k : ℕ) : LocalODEFlowOrder.{u} k := by
  induction k with
  | zero =>
    intro E _ _ _ _ F U z₀ hF hU hz₀
    obtain ⟨r,hr,ε,hε,φ,V,hφ,hV,hi,hs,hx,hJ⟩ := exists_C1_local_ODE_flow
      ((hF.contDiffAt (hU.mem_nhds hz₀)).of_le (by simp)) hU hz₀
    exact ⟨r,hr,ε,hε,φ,V,hφ.of_le (by norm_num),hV,hi,hs,hx,hJ⟩
  | succ k ih =>
    intro E _ _ _ _ F U z₀ hF hU hz₀
    let p₀ : E × (E →L[ℝ] E) := (z₀,ContinuousLinearMap.id ℝ E)
    have hFat : ContDiffAt ℝ ∞ F z₀ := hF.contDiffAt (hU.mem_nhds hz₀)
    have hTFat := odeVariationField_contDiffAt_infty hFat (ContinuousLinearMap.id ℝ E)
    obtain ⟨K,W,hW,hLip⟩ := (hTFat.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).exists_lipschitzOnWith
    have hpU : p₀ ∈ U ×ˢ (Set.univ : Set (E →L[ℝ] E)) := ⟨hz₀,Set.mem_univ _⟩
    obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp
      (inter_mem hW ((hU.prod isOpen_univ).mem_nhds hpU))
    let B := Metric.ball p₀ δ
    have hB : IsOpen B := Metric.isOpen_ball
    have hBp : p₀ ∈ B := Metric.mem_ball_self hδ
    have hLipB : LipschitzOnWith K (odeVariationField F) B :=
      hLip.mono (fun p hp => (hδsub hp).1)
    have hTF : ContDiffOn ℝ ∞ (odeVariationField F) B := by
      intro p hp
      exact (odeVariationField_contDiffAt_infty
        (hF.contDiffAt (hU.mem_nhds (hδsub hp).2.1)) p.2).contDiffWithinAt
    obtain ⟨rT,hrT,εT,hεT,ψ,VT,hψ,hVT,hiT,hsT,hxT,hJT⟩ :=
      ih (E × (E →L[ℝ] E)) (odeVariationField F) B p₀ hTF hB hBp
    obtain ⟨r₀,hr₀,ε₀,hε₀,φ,V,hφ,hV,hi,hs,hx,hJ⟩ :=
      exists_C1_local_ODE_flow (hFat.of_le (by simp)) hU hz₀
    let Q₀ := Metric.ball z₀ r₀ ×ˢ Set.Ioo (-ε₀) ε₀
    let P : E × ℝ → E × (E →L[ℝ] E) := fun p => (φ p.1 p.2,V p.1 p.2)
    have hQ₀ : IsOpen Q₀ := Metric.isOpen_ball.prod isOpen_Ioo
    have h₀ : (z₀,(0 : ℝ)) ∈ Q₀ := ⟨Metric.mem_ball_self hr₀,by constructor <;> linarith⟩
    have hPc : ContinuousAt P (z₀,(0 : ℝ)) :=
      (hφ.continuousOn.prodMk hV).continuousAt (hQ₀.mem_nhds h₀)
    have hP₀ : P (z₀,0) = p₀ := Prod.ext (hi z₀ (Metric.mem_ball_self hr₀)).1
      (hi z₀ (Metric.mem_ball_self hr₀)).2
    have hpre : P ⁻¹' B ∈ 𝓝 (z₀,(0 : ℝ)) :=
      hPc.preimage_mem_nhds (hP₀.symm ▸ hB.mem_nhds hBp)
    rw [nhds_prod_eq] at hpre
    obtain ⟨W₀,hW₀,J₀,hJ₀,hsub⟩ := Filter.mem_prod_iff.mp hpre
    obtain ⟨rP,hrP,hrPsub⟩ := Metric.mem_nhds_iff.mp hW₀
    obtain ⟨εP,hεP,hεPsub⟩ := Metric.mem_nhds_iff.mp hJ₀
    let r := min (r₀/2) (min (rT/2) (rP/2))
    let ε := min (ε₀/2) (min (εT/2) (εP/2))
    have hr : 0 < r := lt_min (half_pos hr₀) (lt_min (half_pos hrT) (half_pos hrP))
    have hε : 0 < ε := lt_min (half_pos hε₀) (lt_min (half_pos hεT) (half_pos hεP))
    have hrr₀ : r < r₀ := (min_le_left _ _).trans_lt (half_lt_self hr₀)
    have hrrT : r < rT := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hrT)
    have hrrP : r < rP := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (half_lt_self hrP)
    have he₀ : ε < ε₀ := (min_le_left _ _).trans_lt (half_lt_self hε₀)
    have heT : ε < εT := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hεT)
    have heP : ε < εP := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (half_lt_self hεP)
    let Q := Metric.ball z₀ r ×ˢ Set.Ioo (-ε) ε
    have hQ : IsOpen Q := Metric.isOpen_ball.prod isOpen_Ioo
    have hbase : Q ⊆ Q₀ := by
      intro p hp
      exact ⟨Metric.ball_subset_ball hrr₀.le hp.1,by constructor <;> linarith [hp.2.1,hp.2.2]⟩
    have hlift : ∀ p ∈ Q,
        ((p.1,ContinuousLinearMap.id ℝ E),p.2) ∈
          Metric.ball p₀ rT ×ˢ Set.Ioo (-εT) εT := by
      intro p hp
      constructor
      · rw [Metric.mem_ball,Prod.dist_eq,dist_self,max_eq_left dist_nonneg]
        exact (Metric.mem_ball.mp hp.1).trans hrrT
      · constructor <;> linarith [hp.2.1,hp.2.2]
    have hPB : ∀ p ∈ Q, P p ∈ B := by
      intro p hp
      apply hsub
      refine ⟨hrPsub (Metric.ball_subset_ball hrrP.le hp.1), hεPsub ?_⟩
      rw [Real.ball_eq_Ioo]
      constructor <;> linarith [hp.2.1,hp.2.2]
    have hzsmall (z : E) (hz : z ∈ Metric.ball z₀ r) :
        (z,(0 : ℝ)) ∈ Q := ⟨hz,by constructor <;> linarith⟩
    have heq : ∀ p ∈ Q, P p = ψ (p.1,ContinuousLinearMap.id ℝ E) p.2 := by
      intro p hp
      have hp₀ := hlift (p.1,0) (hzsmall p.1 hp.1)
      have heq₀ : P (p.1,0) = ψ (p.1,ContinuousLinearMap.id ℝ E) 0 := by
        rw [(hiT _ hp₀.1).1]
        exact Prod.ext (hi p.1 (hbase (hzsmall p.1 hp.1)).1).1
          (hi p.1 (hbase (hzsmall p.1 hp.1)).1).2
      have H := ODE_solution_unique_of_mem_Ioo
        (v := fun _ => odeVariationField F) (s := fun _ => B) (K := K)
        (fun _ _ => hLipB) (show (0 : ℝ) ∈ Set.Ioo (-ε) ε by constructor <;> linarith)
        (f := fun t => P (p.1,t))
        (g := ψ (p.1,ContinuousLinearMap.id ℝ E))
        (fun t ht => by
          have hpt : (p.1,t) ∈ Q := ⟨hp.1,ht⟩
          have H := hs p.1 (hbase hpt).1 t (hbase hpt).2
          exact ⟨H.2.1.prodMk H.2.2,hPB _ hpt⟩)
        (fun t ht => by
          have H := hsT _ hp₀.1 t (hlift (p.1,t) ⟨hp.1,ht⟩).2
          exact ⟨H.2.1,H.1⟩) heq₀
      exact H hp.2
    have hκ : ContDiff ℝ k
        (fun p : E × ℝ => ((p.1,ContinuousLinearMap.id ℝ E),p.2)) :=
      (contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd
    have hpair : ContDiffOn ℝ k
        (fun p : E × ℝ => ψ (p.1,ContinuousLinearMap.id ℝ E) p.2) Q :=
      hψ.comp hκ.contDiffOn hlift
    have hφk : ContDiffOn ℝ k (Function.uncurry φ) Q :=
      hpair.fst.congr (fun p hp => congrArg Prod.fst (heq p hp))
    have hVk : ContDiffOn ℝ k (Function.uncurry V) Q :=
      hpair.snd.congr (fun p hp => congrArg Prod.snd (heq p hp))
    have hFφ : ContDiffOn ℝ k (fun p : E × ℝ => F (φ p.1 p.2)) Q :=
      (hF.of_le (by simp)).comp hφk (fun p hp => (hs p.1 (hbase hp).1 p.2 (hbase hp).2).1)
    let J : E × ℝ → (E × ℝ) →L[ℝ] E := fun p =>
      (V p.1 p.2).coprod (ContinuousLinearMap.toSpanSingleton ℝ (F (φ p.1 p.2)))
    have hJk : ContDiffOn ℝ k J Q := by
      apply contDiffOn_clm_apply.mpr
      intro w
      change ContDiffOn ℝ k (fun p : E × ℝ => V p.1 p.2 w.1 + w.2 • F (φ p.1 p.2)) Q
      exact (hVk.clm_apply contDiffOn_const).add (contDiffOn_const.smul hFφ)
    have hderiv : ContDiffOn ℝ k (fderiv ℝ (Function.uncurry φ)) Q :=
      hJk.congr (fun p hp => (hJ p (hbase hp)).fderiv)
    have hsucc : ContDiffOn ℝ ((k : ℕ∞ω)+1) (Function.uncurry φ) Q := by
      rw [contDiffOn_succ_iff_fderiv_of_isOpen hQ]
      exact ⟨fun p hp => (hJ p (hbase hp)).differentiableAt.differentiableWithinAt,by simp,hderiv⟩
    refine ⟨r,hr,ε,hε,φ,V,?_,hV.mono hbase,?_,?_,?_,?_⟩
    · simpa only [Nat.cast_add,Nat.cast_one] using hsucc
    · intro z hz
      exact hi z (hbase (hzsmall z hz)).1
    · intro z hz t ht
      have hpt : (z,t) ∈ Q := ⟨hz,ht⟩
      exact hs z (hbase hpt).1 t (hbase hpt).2
    · intro p hp
      exact hx p (hbase hp)
    · intro p hp
      exact hJ p (hbase hp)

end Yau.LeafProofs.L23Aux

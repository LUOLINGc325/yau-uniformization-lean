import Yau.Proofs.P06HodgeEnergyCore

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ENNReal

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

def hodgeEnergyActualTuple (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M 2) (dA : RealForm M 3) (δA : RealForm M 1)
    (hA : L2RealForm g.form μ A) (hdA : L2RealForm g.form μ dA) (hδA : L2RealForm g.form μ δA) :
    HodgeEnergyAmbient g μ :=
  WithLp.toLp 2 (realizeActualForm g μ A hA,
    WithLp.toLp 2 (realizeActualForm g μ dA hdA, realizeActualForm g μ δA hδA))

theorem hodgeEnergyTuple_tendsto {ι : Type*} {l : Filter ι}
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    {u : ι → L2FormHilbert g μ 2} {d : ι → L2FormHilbert g μ 3} {δ : ι → L2FormHilbert g μ 1}
    {a : L2FormHilbert g μ 2} {b : L2FormHilbert g μ 3} {c : L2FormHilbert g μ 1}
    (hu : Tendsto u l (𝓝 a)) (hd : Tendsto d l (𝓝 b)) (hδ : Tendsto δ l (𝓝 c)) :
    Tendsto (fun i => WithLp.toLp 2 (u i, WithLp.toLp 2 (d i, δ i))) l
      (𝓝 (WithLp.toLp 2 (a, WithLp.toLp 2 (b, c)) : HodgeEnergyAmbient g μ)) := by
  have hrest := (WithLp.prod_continuous_toLp 2 (L2FormHilbert g μ 3) (L2FormHilbert g μ 1)).tendsto (b, c)
    |>.comp (hd.prodMk_nhds hδ)
  exact ((WithLp.prod_continuous_toLp 2 (L2FormHilbert g μ 2)
    (WithLp 2 (L2FormHilbert g μ 3 × L2FormHilbert g μ 1))).tendsto _).comp (hu.prodMk_nhds hrest)

/-- The actual closed triple Hilbert space is exactly the frozen
prequotient d/δ graph closure, with the same compact smooth sequence. -/
theorem hodgeEnergyActualTuple_mem_iff (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2) (dA : RealForm M 3) (δA : RealForm M 1)
    (hA : L2RealForm g.form μ A) (hdA : L2RealForm g.form μ dA) (hδA : L2RealForm g.form μ δA) :
    hodgeEnergyActualTuple g μ A dA δA hA hdA hδA ∈ hodgeEnergySubmodule g μ hμ ↔
      HodgeFormGraphClosure g.form μ A dA δA := by
  classical
  rw [← SetLike.mem_coe, hodgeEnergySubmodule_eq_closure]
  constructor
  · intro h
    obtain ⟨p, hp, ht⟩ := mem_closure_iff_seq_limit.mp h
    choose As hs hc he using hp
    have ht' : Tendsto (fun j => hodgeEnergyCoreTuple g μ hμ (As j) (hs j) (hc j)) atTop
        (𝓝 (hodgeEnergyActualTuple g μ A dA δA hA hdA hδA)) :=
      ht.congr' (Eventually.of_forall he)
    let ua (j : ℕ) := L2FormSpace.ofSection (As j)
      (smooth_compactlySupported_l2RealForm g μ hμ _ (hs j) (hc j))
    let ud (j : ℕ) := L2FormSpace.ofSection (exteriorRealForm (As j))
      (exteriorRealForm_l2 g μ hμ _ (hs j) (hc j))
    let uδ (j : ℕ) := L2FormSpace.ofSection (codifferentialRealForm g.form (As j))
      (codifferentialRealForm_l2 g μ hμ _ (hs j) (hc j))
    have hta : Tendsto (fun j => realizeL2Form g μ (ua j)) atTop
        (𝓝 (realizeL2Form g μ (L2FormSpace.ofSection A hA))) :=
      ((WithLp.fstL 2 ℝ (L2FormHilbert g μ 2)
        (WithLp 2 (L2FormHilbert g μ 3 × L2FormHilbert g μ 1))).continuous.tendsto _).comp ht'
    have htd : Tendsto (fun j => realizeL2Form g μ (ud j)) atTop
        (𝓝 (realizeL2Form g μ (L2FormSpace.ofSection dA hdA))) :=
      (((WithLp.fstL 2 ℝ (L2FormHilbert g μ 3) (L2FormHilbert g μ 1)).comp
        (WithLp.sndL 2 ℝ (L2FormHilbert g μ 2)
          (WithLp 2 (L2FormHilbert g μ 3 × L2FormHilbert g μ 1)))).continuous.tendsto _).comp ht'
    have htδ : Tendsto (fun j => realizeL2Form g μ (uδ j)) atTop
        (𝓝 (realizeL2Form g μ (L2FormSpace.ofSection δA hδA))) :=
      (((WithLp.sndL 2 ℝ (L2FormHilbert g μ 3) (L2FormHilbert g μ 1)).comp
        (WithLp.sndL 2 ℝ (L2FormHilbert g μ 2)
          (WithLp 2 (L2FormHilbert g μ 3 × L2FormHilbert g μ 1)))).continuous.tendsto _).comp ht'
    have hta' := (tendsto_realizeL2Form_iff g μ ua (L2FormSpace.ofSection A hA)).mp hta
    have htd' := (tendsto_realizeL2Form_iff g μ ud (L2FormSpace.ofSection dA hdA)).mp htd
    have htδ' := (tendsto_realizeL2Form_iff g μ uδ (L2FormSpace.ofSection δA hδA)).mp htδ
    refine ⟨hA, hdA, hδA, As, (fun j => exteriorRealForm (As j)),
      (fun j => codifferentialRealForm g.form (As j)), ?_, ?_⟩
    · intro j
      exact ⟨hs j, hc j, exteriorRealForm_smooth _ (hs j), exteriorRealForm_represents _ (hs j),
        codifferentialRealForm_smooth g μ hμ _ (hs j), codifferentialRealForm_represents g μ hμ _ (hs j),
        (ua j).toSection_l2, (ud j).toSection_l2, (uδ j).toSection_l2⟩
    · simpa only [ua, ud, uδ, L2FormSpace.toSection_ofSection, zero_add] using (hta'.add htd').add htδ'
  · intro h
    obtain ⟨As, hs, hta, htd, htδ⟩ := formGraph_sequence g μ hμ h
    let ua (j : ℕ) := L2FormSpace.ofSection (As j)
      (smooth_compactlySupported_l2RealForm g μ hμ _ (hs j).1 (hs j).2)
    let ud (j : ℕ) := L2FormSpace.ofSection (exteriorRealForm (As j))
      (exteriorRealForm_l2 g μ hμ _ (hs j).1 (hs j).2)
    let uδ (j : ℕ) := L2FormSpace.ofSection (codifferentialRealForm g.form (As j))
      (codifferentialRealForm_l2 g μ hμ _ (hs j).1 (hs j).2)
    have hta' := (tendsto_realizeL2Form_iff g μ ua (L2FormSpace.ofSection A hA)).mpr hta
    have htd' := (tendsto_realizeL2Form_iff g μ ud (L2FormSpace.ofSection dA hdA)).mpr htd
    have htδ' := (tendsto_realizeL2Form_iff g μ uδ (L2FormSpace.ofSection δA hδA)).mpr htδ
    exact mem_closure_of_tendsto (hodgeEnergyTuple_tendsto g μ hta' htd' htδ')
      (Eventually.of_forall fun j => ⟨As j, (hs j).1, (hs j).2, rfl⟩)

end Yau.NodeProofs.P06Aux

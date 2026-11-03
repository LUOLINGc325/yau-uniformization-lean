import Yau.Proofs.P06ScalarSmoothHeatGraphChain
import Yau.Proofs.P06ScalarSmoothHeatFiniteJets

/-! Finite original Hodge graph norms control genuine compact chart
jets. No positive smoothing time is fixed in this estimate. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff BoundedContinuousFunction InnerProductSpace

namespace Yau.NodeProofs.P06Aux.ScalarSmooth
open Yau Yau.LeafProofs Yau.LeafProofs.L03 Yau.LeafProofs.L16Aux

variable {n k : ℕ} {M : ComplexManifold n}

def finiteChartProjection {α : Type} [Fintype α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (N : ℕ) (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) (c : α) :
    hodgeGraphChains g μ hμ k N →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin (Fintype.card (RIdx n)) → ℝ)) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (hodgeRegularityFinEquiv n).symm
    (hodgeRegularityFinEquiv_symm_measurePreserving n)).toContinuousLinearMap.comp
      ((chartProjection g μ hμ x χ hχ hcχ hχO (b.coord c).toContinuousLinearMap).comp
        (graphChainEval _ _ N 0))

theorem finiteChartProjection_finiteJet {α : Type} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (N : ℕ) (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) (c : α)
    (f : hodgeGraphChains g μ hμ k N) :
    ∃ u J, FiniteCoordinateWeakJet N u J ∧
      u =ᵐ[volume] (finiteChartProjection g μ hμ N x b χ hχ hcχ hχO c f :
        (Fin (Fintype.card (RIdx n)) → ℝ) → ℝ) ∧
      ∀ w, tsupport (J w) ⊆ (hodgeRegularityFinEquiv n) '' tsupport χ := by
  let E := hodgeRegularityFinEquiv n
  let us := hodgeGraphChainExtend g μ hμ N f
  obtain ⟨A,hA,hAf⟩ := l2FormHilbert_exists_section g μ (f.val 0)
  change realizeActualForm g μ A hA = f.val 0 at hAf
  have hA0 : realizeActualForm g μ A hA = us 0 := by
    simpa [us,hodgeGraphChainExtend,realizeActualForm] using hAf
  obtain ⟨J,hJ,hJK⟩ := hodgeHilbertGraph_chain_cutoff_weakJet g μ hμ N us
    (hodgeGraphChainExtend_edge g μ hμ N f) A hA hA0 x b χ hχ hcχ hχO
  let U := fun y => χ (E.symm y) * hodgeRegularityCoord b A x (E.symm y) c
  let Jf := fun (w : List (Fin (Fintype.card (RIdx n)))) y =>
    J (w.map (Fintype.equivFin (RIdx n)).symm) (E.symm y) c
  have hJf : FiniteCoordinateWeakJet N U Jf :=
    hodgeRegularityFiniteCoordinateWeakJet N _ J hJ
      (fun w _ c => hcχ.of_isClosed_subset (isClosed_tsupport _) (hJK w c)) c
  have hPAE := chartProjection_actual_ae g μ hμ x χ hχ hcχ hχO
    (b.coord c).toContinuousLinearMap A hA
  rw [hAf] at hPAE
  have hp := (hodgeRegularityFinEquiv_symm_measurePreserving n).quasiMeasurePreserving.ae hPAE
  have hc := Lp.coeFn_compMeasurePreserving
    (chartProjection g μ hμ x χ hχ hcχ hχO (b.coord c).toContinuousLinearMap (f.val 0))
    (hodgeRegularityFinEquiv_symm_measurePreserving n)
  refine ⟨U,Jf,hJf,?_,?_⟩
  · filter_upwards [hp,hc] with y hy hcy
    change U y = _
    dsimp only [U,E]
    have hy' : (chartProjection g μ hμ x χ hχ hcχ hχO (b.coord c).toContinuousLinearMap
        (f.val 0)) ((hodgeRegularityFinEquiv n).symm y) =
        χ ((hodgeRegularityFinEquiv n).symm y) *
          hodgeRegularityCoord b A x ((hodgeRegularityFinEquiv n).symm y) c := by
      simpa only [chartFunctional,hodgeRegularityCoord,
        LinearMap.coe_toContinuousLinearMap',Basis.coord_apply] using hy
    exact hy'.symm.trans hcy.symm
  · intro w
    apply closure_minimal _ (hcχ.image E.continuous).isClosed
    intro y hy
    exact ⟨E.symm y,hJK _ c (subset_closure hy),E.apply_symm_apply y⟩

theorem exists_finiteGraphJetCLM {α : Type} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (N : ℕ) (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) (c : α)
    (w : List (Fin (Fintype.card (RIdx n)))) (hN : w.length + Fintype.card (RIdx n) ≤ N) :
    ∃ L : hodgeGraphChains g μ hμ k N →L[ℝ]
        ((Fin (Fintype.card (RIdx n)) → ℝ) →ᵇ ℝ),
      (∀ f, tsupport (L f : (Fin (Fintype.card (RIdx n)) → ℝ) → ℝ) ⊆
        (hodgeRegularityFinEquiv n) '' tsupport χ) ∧ ∀ f φ,
      regularityTest Set.univ φ → (∫ z, L f z * φ z) =
        (-1 : ℝ)^w.length * ∫ z, finiteChartProjection g μ hμ N x b χ hχ hcχ hχO c f z *
          regularityCoefficientWord (fun i => Pi.single i 1) w.reverse φ z := by
  apply finiteWeakJet_boundedLift (finiteChartProjection g μ hμ N x b χ hχ hcχ hχO c) w hN
    (hcχ.image (hodgeRegularityFinEquiv n).continuous)
  intro f
  obtain ⟨u,J,hJ,hAE,hJK⟩ := finiteChartProjection_finiteJet g μ hμ N x b χ hχ hcχ hχO c f
  exact ⟨u,J,hJ,hAE,hJK w⟩

end Yau.NodeProofs.P06Aux.ScalarSmooth

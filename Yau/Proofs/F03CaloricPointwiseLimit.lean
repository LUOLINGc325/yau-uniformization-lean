import Yau.Proofs.F03CaloricGraphCauchy
import Yau.Proofs.F03CaloricRepresentativeLimits

/-! Empty-word C(L) continuity identifies the original pointwise limit everywhere. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates LeafProofs.L16Aux
variable {d : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000

theorem classicalCaloric_pointwise_limit_smooth_of_value_cauchy
    (hd : 0 < d) (O : Set (Space d)) (l r lam upper : ℝ) (hO : IsOpen O)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ)
    (hAB : SmoothCoefficients (O ×ˢ Ioo l r) a b) (hEll : Elliptic (O ×ˢ Ioo l r) a lam upper)
    (u : ℕ → Point d → ℝ) (v : Point d → ℝ)
    (hu : ∀ j, ContDiffOn ℝ ∞ (u j) (O ×ˢ Ioo l r))
    (hClass : ∀ j p,p ∈ O ×ˢ Ioo l r → linearOp (O ×ˢ Ioo l r) a b (u j) p=0)
    (hf : ∀ j, MemLp (u j) 2 (volume.restrict (O ×ˢ Ioo l r)))
    (hCauchy : CauchySeq (fun j => (hf j).toLp (u j)))
    (hPoint : ∀ p ∈ O ×ˢ Ioo l r,Tendsto (fun j => u j p) atTop (𝓝 (v p))) :
    ContDiffOn ℝ ∞ v (O ×ˢ Ioo l r) ∧
      ∀ p ∈ O ×ˢ Ioo l r,linearOp (O ×ˢ Ioo l r) a b v p=0 := by
  have hLocal : ∀ p ∈ O ×ˢ Ioo l r,∃ (V : Set (Space d)) (c e : ℝ) (w : Point d → ℝ),
      IsOpen V ∧ p ∈ V ×ˢ Ioo c e ∧ V ×ˢ Ioo c e ⊆ O ×ˢ Ioo l r ∧
      ContDiffOn ℝ ∞ w (V ×ˢ Ioo c e) ∧ EqOn v w (V ×ˢ Ioo c e) ∧
      ∀ q ∈ V ×ˢ Ioo c e,linearOp (V ×ˢ Ioo c e) a b w q=0 := by
    intro p hp
    obtain ⟨V,c,e,hV,hVc,hVO,hI,hCover⟩ := compact_subset_relcompact_cylinder hO isCompact_singleton
      (singleton_subset_iff.mpr hp)
    have hpV := hCover (mem_singleton p)
    have hce : c < e := hpV.2.1.trans hpV.2.2
    have hVD : V ×ˢ Ioo c e ⊆ O ×ˢ Ioo l r :=
      prod_mono (subset_closure.trans hVO) (Ioo_subset_Icc_self.trans hI)
    let hABV : SmoothCoefficients (V ×ˢ Ioo c e) a b :=
      ⟨hAB.1.mono hVD,fun i => (hAB.2 i).mono hVD⟩
    let hEllV : Elliptic (V ×ˢ Ioo c e) a lam upper :=
      ⟨hEll.1,hEll.2.1,fun q hq => hEll.2.2 q (hVD hq)⟩
    obtain ⟨ev,hEv,hAE⟩ := classicalCaloric_inner_pair_cauchy O V l r c e lam upper hO hV hVc hVO hI
      a b hAB hEll u hu hClass hf hCauchy
    obtain ⟨z,hz⟩ := cauchySeq_tendsto_of_complete hEv
    let w := caloricRepresentative hd V c e lam upper hV hce a b hABV hEllV z
    have hw := caloricRepresentative_spec hd V c e lam upper hV hce a b hABV hEllV z
    have hEach : ∀ j,EqOn (caloricRepresentative hd V c e lam upper hV hce a b hABV hEllV (ev j))
        (u j) (V ×ˢ Ioo c e) := fun j =>
      caloricRepresentative_eqOn_of_ae hd V c e lam upper hV hce a b hABV hEllV (ev j) (u j)
        ((hu j).continuousOn.mono hVD) (hAE j)
    have hAgree : EqOn v w (V ×ˢ Ioo c e) := by
      intro q hq
      have hRep := caloricRepresentative_tendsto_at hd V c e lam upper hV hce a b hABV hEllV
        ev z hz q hq
      have hU : Tendsto (fun j => u j q) atTop (𝓝 (w q)) := by
        convert hRep using 1
        funext j
        exact (hEach j hq).symm
      exact tendsto_nhds_unique (hPoint q (hVD hq)) hU
    exact ⟨V,c,e,w,hV,hpV,hVD,hw.1,hAgree,hw.2.2⟩
  refine ⟨?_,?_⟩
  · apply contDiffOn_of_locally_contDiffOn
    intro p hp
    obtain ⟨V,c,e,w,hV,hpV,hVD,hw,hAgree,_⟩ := hLocal p hp
    exact ⟨V ×ˢ Ioo c e,hV.prod isOpen_Ioo,hpV,(hw.congr hAgree).mono inter_subset_right⟩
  · intro p hp
    obtain ⟨V,c,e,w,hV,hpV,hVD,_hw,hAgree,hPDE⟩ := hLocal p hp
    have hgerm : v =ᶠ[𝓝 p] w := by
      filter_upwards [(hV.prod isOpen_Ioo).mem_nhds hpV] with q hq
      exact hAgree hq
    exact (linearOp_congr_open_sets (hO.prod isOpen_Ioo) (hV.prod isOpen_Ioo) a b hp hpV hgerm).trans
      (hPDE p hpV)

end Yau.Proofs.F03Aux

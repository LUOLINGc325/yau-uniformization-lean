import Yau.Proofs.E02ProductLocalization
import Yau.Proofs.E02SourceCompact
import Yau.Proofs.E02InteriorSourceChoice
import Yau.Proofs.E02PackedGlobalSequence
import Yau.Proofs.E02ActualContactCluster
import Yau.Proofs.E02EventualContactMajorants
import Yau.Proofs.E02ContactCoefficientLimit
import Yau.Proofs.E02BaseTimeJets

open Matrix Set Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder InnerProductSpace
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

private theorem inverse_mem_image {E F : Type*} (e : E ≃ F) (S : Set E) {q : F}
    (hq : q ∈ e '' S) : e.symm q ∈ S := by
  obtain ⟨p,hp,rfl⟩ := hq
  simpa only [Equiv.symm_apply_apply] using hp

/-- The full original fixed-list construction: actual localization,
source compactum, global Jensen contacts, genuine attained source tests,
epsilon FIRST, then κ. The ORIGINAL B was fixed before this list. -/
theorem fixed_list_original_majorant {n m : ℕ}
    (X : KahlerManifold n) (h : Flow X) (ρ : STF X)
    (hh : MetricFamilySmooth h (Ici 0)) (hoc : OptimizerContacts X h ρ)
    (hV01 : EnvelopeInequality X h) (T : ℝ) (hT : 0 < T) (x : Pt X)
    (a₀ : ComplexVector n × ℝ) (hz : a₀.1 ∈ chartTarget x) (ht : a₀.2 ∈ Ioo 0 T)
    (B : Herm n) (hB : FeasibleEllipsoid X h T x a₀.1 a₀.2 B)
    (hMax : ∀ D, FeasibleEllipsoid X h T x a₀.1 a₀.2 D → D.det.re ≤ B.det.re)
    (α : Fin m → ℝ) (hα : ∀ i, 0 < α i) (η₀ : Fin m → ComplexVector n)
    (hGram₀ : weightedColumns α η₀*(weightedColumns α η₀)ᴴ = B⁻¹)
    (hEnv : ∀ i, envelopeChart h T x (a₀.1,η₀ i,a₀.2) = 1)
    (hq₀ : ∀ i, qform B (η₀ i) = 1) (hSum : ∑ i, α i = n)
    (f : ComplexVector n × ℝ → ℝ) (hf : ContDiffAt ℝ ∞ f a₀)
    (hValue : f a₀ = ellipsoidLogDet X h T x a₀.1 a₀.2)
    (hLower : ∀ᶠ p in 𝓝 a₀, f p ≤ ellipsoidLogDet X h T x p.1 p.2)
    (θ w : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hw : w < 1) (hWeight : ∀ i, α i ≤ w) :
    ∃ L : Herm n, L.PosSemidef ∧ (L-leviC (fun z => f (z,a₀.2)) a₀.1).PosSemidef ∧
      ((1-θ)*(1-w))*tracePair B L ≤ deriv (fun t => f (a₀.1,t)) a₀.2 := by
  obtain ⟨V,O,γ,hV,haV,hVD,hfV,hO,hCO,hOC,hOU,hStar,hγ,hGap,hCenter,hNonneg,hZero⟩ :=
    exists_original_product_localization X h ρ hoc T hT x a₀ hz ht B hB hMax α hα η₀ hGram₀
      hEnv hSum f hf hValue hLower θ hθ₀
  let e := productRealCoordinates n m
  let fS := baseTimeStrictify f a₀
  let P₀ := rowProjector (weightedColumns α η₀)
  obtain ⟨K,S,M,hK,hNE,hSC,_hSNE,hSK,hM,hKD,hv,hBound,hProjS⟩ :=
    exists_original_source_compact X h hh T x a₀ ⟨hz,ht⟩ O hOC
      (fun Q hQ _ => ⟨(hVD (hOU hQ).1).1,(hVD (hOU hQ).1).2⟩)
  have hv0 : ∀ q ∈ K, 0 ≤ packedEnvelopeReal X h T x q := fun q hq => (hBound q hq).1
  have hUp : ∀ q ∈ K, packedEnvelopeReal X h T x q ≤ M := fun q hq => (hBound q hq).2
  have hProjK : ∀ Q ∈ closure O, ∀ i, factorProjection n m i (productRealCoordinates n m Q) ∈ K := by
    intro Q hQ i
    exact interior_subset (hSK (hProjS Q hQ i))
  obtain ⟨κ₀,hκ₀,hSources⟩ := exists_interior_source_choice_scale X h T x K S hK hNE hSC hSK
    hv hv0 M hM.le hUp
  obtain ⟨κ,R,slope,p,A,hκ,hκLim,hSlopeLim,hData⟩ :=
    exists_original_packed_global_sequence X h T x fS α (fun i => (hα i).le) P₀ θ V hV hfV
      O hO hOC hOU (a₀.1,a₀.2,η₀) hStar K hK hNE hv hv0 M hM.le hUp
      hProjK hCenter.le γ κ₀ hγ hκ₀ hGap
  have hRSource (j : ℕ) : ∀ i, factorProjection n m i (R j) ∈ S := by
    obtain ⟨Q,hQ,hQR⟩ := (hData j).1
    intro i
    rw [←hQR]
    exact hProjS Q (subset_closure hQ) i
  choose src hSrc hSrcMin using (fun j => hSources (κ j) (hκ j).1 (hκ j).2 (R j) (hRSource j))
  have hRC : IsCompact (e '' closure O) := hOC.image e.continuous
  have hRCl (j : ℕ) : R j ∈ e '' closure O := image_mono subset_closure (hData j).1
  obtain ⟨R₀,hR₀,φ,hφ,hRLim⟩ := hRC.tendsto_subseq hRCl
  have hφLim : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hGlobal (j : ℕ) : ∀ Z ∈ (productRealCoordinates n m) '' closure O,
      ((∑ i, α i*compactInfConvolution K (packedEnvelopeReal X h T x) (κ j) (factorProjection n m i (R j)))-
        productCostPacked fS α P₀ θ (R j))-⟪slope j,R j⟫_ℝ ≤
      ((∑ i, α i*compactInfConvolution K (packedEnvelopeReal X h T x) (κ j) (factorProjection n m i Z))-
        productCostPacked fS α P₀ θ Z)-⟪slope j,Z⟫_ℝ := by
    intro Z hZ
    apply (hData j).2.2.1 Z
    have hClosure : closure ((productRealCoordinates n m) '' O) =
        (productRealCoordinates n m) '' closure O :=
      ((productRealCoordinates n m).toHomeomorph.image_closure O).symm
    rwa [hClosure]
  have hRCl' (j : ℕ) : R j ∈ (productRealCoordinates n m) '' closure O := by
    simpa only [e] using hRCl j
  have hR₀' : R₀ ∈ (productRealCoordinates n m) '' closure O := by
    simpa only [e] using hR₀
  have hAtZero : actualProductGap X h T x fS α P₀ θ ((productRealCoordinates n m).symm R₀) = 0 := by
    apply actual_packed_global_minimizer_cluster X h T x fS α (fun i => (hα i).le)
      P₀ θ V hV hfV O hOU K hK hNE hv hv0 M hM.le hUp hProjK hNonneg
      (a₀.1,a₀.2,η₀) (subset_closure hStar) hCenter.le
      (κ ∘ φ) (fun j => (hκ (φ j)).1) (hκLim.comp hφLim)
      (R ∘ φ) (slope ∘ φ) R₀ (fun j => hRCl' (φ j)) hR₀' hRLim
      (hSlopeLim.comp hφLim)
    intro j Z hZ
    simpa only [Function.comp_def] using hGlobal (φ j) Z hZ
  let Q : ℕ → ProductPoint n m := fun j => e.symm (R (φ j))
  let Q₀ : ProductPoint n m := e.symm R₀
  have hQO (j : ℕ) : Q j ∈ O := inverse_mem_image e.toEquiv O (hData (φ j)).1
  have hQ₀ : Q₀ ∈ closure O := inverse_mem_image e.toEquiv (closure O) hR₀
  have hOrbit : Q₀ ∈ contactOrbit a₀ α B P₀ := hZero Q₀ hQ₀ hAtZero
  have hQLim : Tendsto Q atTop (𝓝 Q₀) := (e.symm.continuous.tendsto R₀).comp hRLim
  have hfQ (j : ℕ) : ContDiffAt ℝ 2 fS ((Q j).1,(Q j).2.1) :=
    hfV.contDiffAt (hV.mem_nhds (hOU (subset_closure (hQO j))).1)
  have hMQ (j : ℕ) : (weightedColumns α (Q j).2.2*(weightedColumns α (Q j).2.2)ᴴ).PosDef :=
    (fullRankRect_iff_posDef _).mp (hOU (subset_closure (hQO j))).2
  have hJetQ (j : ℕ) : ∀ i, RealSecondJet (compactInfConvolution K (packedEnvelopeReal X h T x) (κ (φ j)))
      (factorProjection n m i (productRealCoordinates n m (Q j))) (p (φ j) i) (A (φ j) i) := by
    intro i
    simpa only [Q,e,ContinuousLinearEquiv.apply_symm_apply] using (hData (φ j)).2.2.2 i
  have hMinQ (j : ℕ) : IsLocalMin (fun Z => (∑ i, α i*compactInfConvolution K (packedEnvelopeReal X h T x)
      (κ (φ j)) (factorProjection n m i Z))-productCostPacked fS α P₀ θ Z-⟪slope (φ j),Z⟫_ℝ)
        (productRealCoordinates n m (Q j)) := by
    simpa only [Q,e,ContinuousLinearEquiv.apply_symm_apply] using (hData (φ j)).2.1
  have hSrcMinQ (j : ℕ) : ∀ i, compactInfConvolution K (packedEnvelopeReal X h T x) (κ (φ j))
      (factorProjection n m i (productRealCoordinates n m (Q j))) =
      packedEnvelopeReal X h T x (envelopeRealCoordinates n (src (φ j) i))+
      ‖factorProjection n m i (productRealCoordinates n m (Q j))-envelopeRealCoordinates n (src (φ j) i)‖^2/(2*κ (φ j)) := by
    intro i
    simpa only [Q,e,ContinuousLinearEquiv.apply_symm_apply] using hSrcMin (φ j) i
  obtain ⟨N,L,hL,hLoss⟩ := exists_eventual_contact_majorants X h hV01 T x K hKD (κ ∘ φ)
    (fun j => (hκ (φ j)).1) fS a₀ α hα η₀ B hB.1 hGram₀ hq₀ θ w hθ₀.le hθ₁ hw hWeight
    Q Q₀ hQLim hOrbit hfQ hMQ (p ∘ φ) (A ∘ φ) hJetQ (src ∘ φ)
    (fun j => hSrc (φ j)) hSrcMinQ (slope ∘ φ) hMinQ
  have hBaseLim : Tendsto (fun j => ((Q j).1,(Q j).2.1)) atTop (𝓝 a₀) := by
    have hh := ((productBaseTimeCLM n m).continuous.tendsto Q₀).comp hQLim
    simpa only [Function.comp_def,productBaseTimeCLM_apply,hOrbit.1] using hh
  have hBaseTail := hBaseLim.comp (tendsto_add_atTop_nat N)
  have hSlopeTail := (hSlopeLim.comp hφLim).comp (tendsto_add_atTop_nat N)
  have hError : Tendsto (fun j => ⟪slope (φ (j+N)),productRealCoordinates n m (0,1,0)⟫_ℝ)
      atTop (𝓝 0) := by
    simpa only [inner_zero_left,Function.comp_def] using
      hSlopeTail.inner (tendsto_const_nhds (x := productRealCoordinates n m (0,1,0)))
  have hc : 0 < (1-θ)*(1-w) := mul_pos (sub_pos.mpr hθ₁) (sub_pos.mpr hw)
  obtain ⟨L₀,hL₀,hDomL₀,hTraceL₀⟩ := exists_actual_base_time_majorant_limit fS a₀
    ((baseTimeStrictify_contDiffAt hf).of_le (by simp)) B hB.1 ((1-θ)*(1-w)) hc
    (fun j => ((Q (j+N)).1,(Q (j+N)).2.1)) hBaseTail
    (fun j => ⟪slope (φ (j+N)),productRealCoordinates n m (0,1,0)⟫_ℝ) hError
    L (fun j => (hL j).1) (fun j => (hL j).2) hLoss
  have hLevi := baseTimeStrictify_leviC hf
  have hTime := baseTimeStrictify_time_deriv hf
  change (L₀-leviC (fun z => baseTimeStrictify f a₀ (z,a₀.2)) a₀.1).PosSemidef at hDomL₀
  rw [hLevi] at hDomL₀
  change ((1-θ)*(1-w))*tracePair B L₀ ≤ deriv (fun t => baseTimeStrictify f a₀ (a₀.1,t)) a₀.2 at hTraceL₀
  rw [hTime] at hTraceL₀
  exact ⟨L₀,hL₀,hDomL₀,hTraceL₀⟩

end Yau.NodeProofs.E02Aux

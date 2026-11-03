import Yau.Proofs.E02PackedCostExtension
import Yau.Proofs.E02JensenContactSequence
import Yau.Proofs.E02EnvelopeV01Test
import Yau.Proofs.E02ActualProductGap

open Matrix Set Filter
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

theorem packed_actualProductGap_eq {n m : ℕ}
    (X : KahlerManifold n) (h : Flow X) (T : ℝ) (x : Pt X)
    (f : ComplexVector n × ℝ → ℝ) (α : Fin m → ℝ) (P₀ : Herm m) (θ : ℝ)
    (Q : ProductPoint n m) :
    (∑ i, α i*packedEnvelopeReal X h T x (factorProjection n m i (productRealCoordinates n m Q)))-
      productCostPacked f α P₀ θ (productRealCoordinates n m Q) =
        actualProductGap X h T x f α P₀ θ Q := by
  simp only [factorProjection_on_product,packedEnvelopeReal,productCostPacked,
    ContinuousLinearEquiv.symm_apply_apply,actualProductGap]

/-- The original physical gap and its genuine C² cost extension produce
actual simultaneous jets whose local minimum uses the ORIGINAL packed
cost. The extension disappears before the contact-form calculus. -/
theorem exists_original_packed_contact_sequence {n m : ℕ}
    (X : KahlerManifold n) (h : Flow X) (T : ℝ) (x : Pt X)
    (f : ComplexVector n × ℝ → ℝ) (α : Fin m → ℝ) (hα : ∀ i, 0 ≤ α i)
    (P₀ : Herm m) (θ : ℝ) (V : Set (ComplexVector n × ℝ)) (hV : IsOpen V)
    (hf : ContDiffOn ℝ 2 f V) (O : Set (ProductPoint n m)) (hO : IsOpen O)
    (hOC : IsCompact (closure O)) (hOU : closure O ⊆ productOpenDomain α V)
    (Qstar : ProductPoint n m) (hStar : Qstar ∈ O)
    (K : Set (EuclideanSpace ℝ (Fin (4*n+1)))) (hK : IsCompact K) (hNE : K.Nonempty)
    (hv : LowerSemicontinuousOn (packedEnvelopeReal X h T x) K)
    (hv0 : ∀ q ∈ K, 0 ≤ packedEnvelopeReal X h T x q)
    (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ q ∈ K, packedEnvelopeReal X h T x q ≤ M)
    (hProj : ∀ Q ∈ closure O, ∀ i, factorProjection n m i (productRealCoordinates n m Q) ∈ K)
    (hCenter : actualProductGap X h T x f α P₀ θ Qstar ≤ 0)
    (γ κmax : ℝ) (hγ : 0 < γ) (hκmax : 0 < κmax)
    (hGap : ∀ Q ∈ frontier O, γ ≤ actualProductGap X h T x f α P₀ θ Q) :
    ∃ (κ : ℕ → ℝ)
      (Q slope : ℕ → EuclideanSpace ℝ (Fin (2*n+1+2*n*m)))
      (p : ℕ → Fin m → EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
      (A : ℕ → Fin m → EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ]
        EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ),
      (∀ j, 0 < κ j ∧ κ j < κmax) ∧ Tendsto κ atTop (𝓝 0) ∧
      Tendsto slope atTop (𝓝 0) ∧ ∀ j, Q j ∈ (productRealCoordinates n m) '' O ∧
        IsLocalMin (fun R => (∑ i, α i*compactInfConvolution K (packedEnvelopeReal X h T x)
          (κ j) (factorProjection n m i R))-productCostPacked f α P₀ θ R-⟪slope j,R⟫_ℝ) (Q j) ∧
        ∀ i, RealSecondJet (compactInfConvolution K (packedEnvelopeReal X h T x) (κ j))
          (factorProjection n m i (Q j)) (p j i) (A j i) := by
  let e := productRealCoordinates n m
  let OR := e '' O
  have hOR : IsOpen OR := e.isOpenMap O hO
  have hClosure : closure OR = e '' closure O := (e.toHomeomorph.image_closure O).symm
  have hORC : IsCompact (closure OR) := by rw [hClosure]; exact hOC.image e.continuous
  obtain ⟨g,C,W,hW,hCW,hEq,hg,_hgC,_hC,hConv⟩ :=
    exists_packed_product_cost_extension f α P₀ θ V hV hf O hOC hOU
  have hPJ : ∀ R ∈ closure OR, ∀ i, factorProjection n m i R ∈ K := by
    intro R hR i
    rw [hClosure] at hR
    obtain ⟨Q,hQ,rfl⟩ := hR
    simpa only [e] using hProj Q hQ i
  have hCenterR : (∑ i, α i*packedEnvelopeReal X h T x (factorProjection n m i (e Qstar)))-g (e Qstar) ≤ 0 := by
    rw [hEq (hCW (subset_closure (mem_image_of_mem e hStar)))]
    simpa only [e,packed_actualProductGap_eq] using hCenter
  have hGapR : ∀ R ∈ closure OR \ OR,
      γ ≤ (∑ i, α i*packedEnvelopeReal X h T x (factorProjection n m i R))-g R := by
    intro R hR
    have hRW := hCW hR.1
    have hRCl := hR.1
    rw [hClosure] at hRCl
    obtain ⟨Q,hQ,rfl⟩ := hRCl
    have hNot : Q ∉ O := fun hQO => hR.2 (mem_image_of_mem e hQO)
    have hFront : Q ∈ frontier O := by
      rw [frontier,hO.interior_eq]
      exact ⟨hQ,hNot⟩
    rw [hEq hRW]
    simpa only [e,packed_actualProductGap_eq] using hGap Q hFront
  obtain ⟨κ,Q,slope,p,A,hκ,hκLim,hSlopeLim,hData⟩ := exists_jensen_contact_sequence n m
    K (packedEnvelopeReal X h T x) hK hNE hv hv0 M hM α hα g hg.continuous C hConv OR hOR hORC
    (e Qstar) (mem_image_of_mem e hStar) hPJ (fun R hR i => hBound _ (hPJ R hR i))
    hCenterR γ κmax hγ hκmax hGapR
  refine ⟨κ,Q,slope,p,A,hκ,hκLim,hSlopeLim,?_⟩
  intro j
  refine ⟨(hData j).1,?_,(hData j).2.2⟩
  exact localMin_sub_cost_of_eqOn
    (fun R => ∑ i, α i*compactInfConvolution K (packedEnvelopeReal X h T x) (κ j) (factorProjection n m i R))
    g (productCostPacked f α P₀ θ) (fun R => ⟪slope j,R⟫_ℝ) W hW (Q j)
    (hCW (subset_closure (hData j).1)) hEq (hData j).2.1

end Yau.NodeProofs.E02Aux

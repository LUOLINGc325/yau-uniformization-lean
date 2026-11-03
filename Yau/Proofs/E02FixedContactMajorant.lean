import Yau.Proofs.E02JetMajorant
import Yau.Proofs.E02SchurAggregate
import Yau.Proofs.E02ProductContactForms
import Yau.Proofs.E02ProjectorLeviBound
import Yau.Proofs.E02WeightedTraceEstimate

open Matrix Set Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder InnerProductSpace
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- At one ACTUAL shared κ-contact, remove ε at each actual attained
source, independently minimize the complex vertical variables, and form
ONE PSD horizontal majorant. All coefficient losses use this same matrix. -/
theorem fixed_contact_psd_majorant {n m : ℕ}
    (X : KahlerManifold n) (h : Flow X) (hV : EnvelopeInequality X h) (T : ℝ) (x : Pt X)
    (K : Set (EuclideanSpace ℝ (Fin (4*n+1))))
    (hDom : ∀ q ∈ K, (envelopeRealCoordinates n).symm q ∈ envelopeDomain X T x)
    {κ : ℝ} (hκ : 0 < κ) (f : ComplexVector n × ℝ → ℝ)
    (α : Fin m → ℝ) (hα : ∀ i, 0 < α i) (M₀ : Rect n m) (θ : ℝ)
    (hM₀ : (M₀*M₀ᴴ).PosDef) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (Q : ProductPoint n m) (hf : ContDiffAt ℝ 2 f (Q.1,Q.2.1))
    (hM : (weightedColumns α Q.2.2*(weightedColumns α Q.2.2)ᴴ).PosDef)
    (p : Fin m → EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
    (A : Fin m → EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
    (hJet : ∀ i, RealSecondJet (compactInfConvolution K (packedEnvelopeReal X h T x) κ)
      (factorProjection n m i (productRealCoordinates n m Q)) (p i) (A i))
    (a : Fin m → ComplexVector n × ComplexVector n × ℝ)
    (ha : ∀ i, envelopeRealCoordinates n (a i) ∈ interior K)
    (hMinSource : ∀ i, compactInfConvolution K (packedEnvelopeReal X h T x) κ
      (factorProjection n m i (productRealCoordinates n m Q)) =
        packedEnvelopeReal X h T x (envelopeRealCoordinates n (a i))+
        ‖factorProjection n m i (productRealCoordinates n m Q)-envelopeRealCoordinates n (a i)‖^2/(2*κ))
    (hC : ∀ i, (cotangentTensor (A i)).toBlocks₂₂.PosDef)
    (slope : EuclideanSpace ℝ (Fin (2*n+1+2*n*m)) →L[ℝ] ℝ)
    (hMin : IsLocalMin (fun R => (∑ i, α i*compactInfConvolution K (packedEnvelopeReal X h T x) κ
      (factorProjection n m i R))-productCostPacked f α (rowProjector M₀) θ R-slope R)
        (productRealCoordinates n m Q)) (B : Herm n) :
    ∃ L : Herm n, L.PosSemidef ∧ (L-leviC (fun z => f (z,Q.2.1)) Q.1).PosSemidef ∧
      ∀ d : ℝ, (∀ i, ((cotangentTensor (A i)).toBlocks₂₂-(d : ℂ) • B).PosSemidef) →
        d*tracePair B L ≤ deriv (fun t => f (Q.1,t)) Q.2.1+
          slope (productRealCoordinates n m (0,1,0)) := by
  choose L hL hDomL hTrace using (fun i => attained_source_jet_majorant X h hV T x K hDom
    hκ (factorProjection n m i (productRealCoordinates n m Q)) (a i) (ha i) (hMinSource i)
    (p i) (A i) (hJet i) (hC i))
  have hRaw := sameContact_productCost_forms n m
    (fun _ => compactInfConvolution K (packedEnvelopeReal X h T x) κ)
    f α (rowProjector M₀) θ Q p A hJet hf hM slope hMin
  have hForms : ∀ (Z : ComplexVector n) (W : Fin m → ComplexVector n),
      (star (WithLp.ofLp Z) ⬝ᵥ (leviC (fun z => f (z,Q.2.1)) Q.1*ᵥWithLp.ofLp Z)).re ≤
        ∑ i, α i*(star (cotangentVector Z (W i)) ⬝ᵥ
          (cotangentTensor (A i)*ᵥcotangentVector Z (W i))).re := by
    intro Z W
    have h1 := hRaw.2 Z W
    have h2 := logGram_sub_penalty_rectLevi_nonneg M₀ (weightedColumns α Q.2.2)
      (weightedColumns α W) hM₀ hM hθ₀ hθ₁
    linarith
  have hSpatial : ContDiffAt ℝ 2 (fun z => f (z,Q.2.1)) Q.1 :=
    hf.comp Q.1 (contDiff_id.prodMk contDiff_const).contDiffAt
  have hHerm : (leviC (fun z => f (z,Q.2.1)) Q.1).IsHermitian :=
    leviMatrix_isHermitian hSpatial stdVec
  have hOrder := weighted_schur_order α (fun i => cotangentTensor (A i))
    (fun i => cotangentTensor_isHermitian (A i) (hJet i).1) hC _ hHerm hForms
  have hMaj := weighted_schur_majorants α (fun i => (hα i).le)
    (fun i => schurComplement (cotangentTensor (A i))) L _ hL hDomL hOrder
  refine ⟨∑ i, (α i : ℂ) • L i,hMaj.1,hMaj.2,?_⟩
  intro d hLower
  have hTotal := weighted_majorant_trace_bound α (fun i => (hα i).le) B d
    (fun i => (cotangentTensor (A i)).toBlocks₂₂) L
    (fun i => p i (envelopeRealCoordinates n (0,0,1))) hLower hL hTrace
  rw [hRaw.1] at hTotal
  exact hTotal

end Yau.NodeProofs.E02Aux

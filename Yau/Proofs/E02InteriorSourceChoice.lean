import Yau.Proofs.E02UniformSourceInterior
import Yau.Proofs.E02EnvelopeV01Test
import Yau.Proofs.E02ProductPacking

open Set
open scoped Topology
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- Actual compact attainment constructs every physical source; the
uniform scale puts them in the source interior before the κ-sequence
or its Peano contacts are selected. -/
theorem exists_interior_source_choice_scale {n m : ℕ}
    (X : KahlerManifold n) (h : Flow X) (T : ℝ) (x : Pt X)
    (K S : Set (EuclideanSpace ℝ (Fin (4*n+1))))
    (hK : IsCompact K) (hNE : K.Nonempty) (hS : IsCompact S) (hSK : S ⊆ interior K)
    (hv : LowerSemicontinuousOn (packedEnvelopeReal X h T x) K)
    (hv0 : ∀ q ∈ K, 0 ≤ packedEnvelopeReal X h T x q)
    (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ q ∈ K, packedEnvelopeReal X h T x q ≤ M) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ < κ₀ →
      ∀ Q : EuclideanSpace ℝ (Fin (2*n+1+2*n*m)), (∀ i, factorProjection n m i Q ∈ S) →
        ∃ a : Fin m → ComplexVector n × ComplexVector n × ℝ, ∀ i,
          envelopeRealCoordinates n (a i) ∈ interior K ∧
          compactInfConvolution K (packedEnvelopeReal X h T x) κ (factorProjection n m i Q) =
            packedEnvelopeReal X h T x (envelopeRealCoordinates n (a i))+
              ‖factorProjection n m i Q-envelopeRealCoordinates n (a i)‖^2/(2*κ) := by
  obtain ⟨κ₀,hκ₀,hSmall⟩ := compactInfConvolution_uniform_source_interior K S hS hSK
    (packedEnvelopeReal X h T x) hv0 M hM
    (fun q hq => hBound q (interior_subset (hSK hq)))
  refine ⟨κ₀,hκ₀,?_⟩
  intro κ hκ hκSmall Q hQ
  choose b hb hEq _hMin using (fun i => compactInfConvolution_attained K (packedEnvelopeReal X h T x)
    hK hNE hv κ (factorProjection n m i Q))
  refine ⟨fun i => (envelopeRealCoordinates n).symm (b i),?_⟩
  intro i
  have hInterior := hSmall κ hκ hκSmall _ (hQ i) (b i) (hb i) (hEq i)
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using And.intro hInterior (hEq i)

end Yau.NodeProofs.E02Aux

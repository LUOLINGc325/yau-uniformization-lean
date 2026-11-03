import Yau.Proofs.E02WeightedCoordinates
import Yau.Proofs.E02ProductCost

open Matrix Set
open scoped Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

def productOpenDomain {n m : ℕ} (α : Fin m → ℝ) (V : Set (ComplexVector n × ℝ)) :
    Set (ProductPoint n m) :=
  {Q | (Q.1,Q.2.1) ∈ V ∧ weightedColumns α Q.2.2 ∈ fullRankRect n m}

theorem isOpen_productOpenDomain {n m : ℕ} (α : Fin m → ℝ)
    (V : Set (ComplexVector n × ℝ)) (hV : IsOpen V) : IsOpen (productOpenDomain α V) :=
  (hV.preimage (productBaseTimeCLM n m).continuous).inter
    ((isOpen_fullRankRect n m).preimage (productColumnsCLM α).continuous)

def contactOrbit {n m : ℕ} (a : ComplexVector n × ℝ) (α : Fin m → ℝ)
    (B : Herm n) (P₀ : Herm m) : Set (ProductPoint n m) :=
  {Q | (Q.1,Q.2.1) = a ∧ weightedColumns α Q.2.2*(weightedColumns α Q.2.2)ᴴ = B⁻¹ ∧
    (weightedColumns α Q.2.2)ᴴ*B*weightedColumns α Q.2.2 = P₀}

theorem isCompact_contactOrbit {n m : ℕ} (a : ComplexVector n × ℝ)
    (α : Fin m → ℝ) (hα : ∀ i, 0 < α i) (B : Herm n) (P₀ : Herm m) :
    IsCompact (contactOrbit a α B P₀) := by
  have hEmb : Continuous (fun η : Fin m → ComplexVector n => (a.1,a.2,η)) :=
    continuous_const.prodMk (continuous_const.prodMk continuous_id)
  have hC := (isCompact_weighted_equality_orbit α hα B⁻¹ B P₀).image hEmb
  have hSet : (fun η : Fin m → ComplexVector n => (a.1,a.2,η)) ''
      {η | weightedColumns α η*(weightedColumns α η)ᴴ = B⁻¹ ∧
        (weightedColumns α η)ᴴ*B*weightedColumns α η = P₀} = contactOrbit a α B P₀ := by
    ext Q
    constructor
    · rintro ⟨η,hη,rfl⟩
      exact ⟨rfl,hη⟩
    · rintro ⟨hBase,hGram,hP⟩
      refine ⟨Q.2.2,⟨hGram,hP⟩,?_⟩
      exact Prod.ext (congrArg Prod.fst hBase).symm
        (Prod.ext (congrArg Prod.snd hBase).symm rfl)
  rwa [hSet] at hC

theorem contactOrbit_subset_productOpenDomain {n m : ℕ}
    (a : ComplexVector n × ℝ) (α : Fin m → ℝ) (B : Herm n) (hB : B.PosDef)
    (P₀ : Herm m) (V : Set (ComplexVector n × ℝ)) (ha : a ∈ V) :
    contactOrbit a α B P₀ ⊆ productOpenDomain α V := by
  intro Q hQ
  refine ⟨?_,(fullRankRect_iff_posDef _).mpr ?_⟩
  · simpa only [hQ.1] using ha
  · rw [hQ.2.1]
    exact hB.inv

theorem original_tuple_mem_contactOrbit {n m : ℕ}
    (a : ComplexVector n × ℝ) (α : Fin m → ℝ) (η : Fin m → ComplexVector n)
    (B : Herm n) (hB : B.PosDef)
    (hGram : weightedColumns α η*(weightedColumns α η)ᴴ = B⁻¹) :
    (a.1,a.2,η) ∈ contactOrbit a α B (rowProjector (weightedColumns α η)) := by
  refine ⟨rfl,hGram,?_⟩
  unfold rowProjector
  rw [hGram,Matrix.nonsing_inv_nonsing_inv _ (hB.isUnit.map Matrix.detMonoidHom)]

theorem productCostPhysical_contDiffOn_domain {n m : ℕ}
    (f : ComplexVector n × ℝ → ℝ) (V : Set (ComplexVector n × ℝ)) (hV : IsOpen V)
    (hf : ContDiffOn ℝ 2 f V) (α : Fin m → ℝ) (P₀ : Herm m) (θ : ℝ) :
    ContDiffOn ℝ 2 (productCostPhysical f α P₀ θ) (productOpenDomain α V) := by
  intro Q hQ
  exact (productCostPhysical_contDiffAt f α P₀ θ Q
    (hf.contDiffAt (hV.mem_nhds hQ.1)) ((fullRankRect_iff_posDef _).mp hQ.2)).contDiffWithinAt

end Yau.NodeProofs.E02Aux

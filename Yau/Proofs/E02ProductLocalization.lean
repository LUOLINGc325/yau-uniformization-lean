import Yau.Proofs.E02ProductDomain
import Yau.Proofs.E02BaseLocalization
import Yau.Proofs.E02ZeroGapOrbit
import Yau.Proofs.E02OriginalContactGap
import Yau.Proofs.E02ProductGapRegularity
import Yau.Proofs.E02CompactNeighborhood

open Matrix Set Filter
open scoped Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- Actual localization around the ENTIRE fixed contact orbit. All
open domains, compactness and the strictly positive boundary gap are
constructed from the original test and its original optimizer. -/
theorem exists_original_product_localization {n m : ℕ}
    (X : KahlerManifold n) (h : Flow X) (ρ : STF X) (hoc : OptimizerContacts X h ρ)
    (T : ℝ) (hT : 0 < T) (x : Pt X) (a : ComplexVector n × ℝ)
    (hz : a.1 ∈ chartTarget x) (ht : a.2 ∈ Ioo 0 T)
    (B : Herm n) (hB : FeasibleEllipsoid X h T x a.1 a.2 B)
    (hMax : ∀ D, FeasibleEllipsoid X h T x a.1 a.2 D → D.det.re ≤ B.det.re)
    (α : Fin m → ℝ) (hα : ∀ i, 0 < α i) (η : Fin m → ComplexVector n)
    (hGram : weightedColumns α η*(weightedColumns α η)ᴴ = B⁻¹)
    (hEnv : ∀ i, envelopeChart h T x (a.1,η i,a.2) = 1) (hSum : ∑ i, α i = n)
    (f : ComplexVector n × ℝ → ℝ) (hf : ContDiffAt ℝ ∞ f a)
    (hValue : f a = ellipsoidLogDet X h T x a.1 a.2)
    (hLower : ∀ᶠ p in 𝓝 a, f p ≤ ellipsoidLogDet X h T x p.1 p.2)
    (θ : ℝ) (hθ : 0 < θ) :
    ∃ (V : Set (ComplexVector n × ℝ)) (O : Set (ProductPoint n m)) (γ : ℝ),
      IsOpen V ∧ a ∈ V ∧ V ⊆ chartTarget x ×ˢ Ioo 0 T ∧
      ContDiffOn ℝ 2 (baseTimeStrictify f a) V ∧ IsOpen O ∧
      contactOrbit a α B (rowProjector (weightedColumns α η)) ⊆ O ∧
      IsCompact (closure O) ∧ closure O ⊆ productOpenDomain α V ∧ (a.1,a.2,η) ∈ O ∧
      0 < γ ∧
      (∀ Q ∈ frontier O, γ ≤ actualProductGap X h T x (baseTimeStrictify f a)
        α (rowProjector (weightedColumns α η)) θ Q) ∧
      actualProductGap X h T x (baseTimeStrictify f a) α
        (rowProjector (weightedColumns α η)) θ (a.1,a.2,η) = 0 ∧
      (∀ Q ∈ closure O, 0 ≤ actualProductGap X h T x (baseTimeStrictify f a)
        α (rowProjector (weightedColumns α η)) θ Q) ∧
      (∀ Q ∈ closure O, actualProductGap X h T x (baseTimeStrictify f a)
        α (rowProjector (weightedColumns α η)) θ Q = 0 →
          Q ∈ contactOrbit a α B (rowProjector (weightedColumns α η))) := by
  obtain ⟨V,hV,haV,hVD,hfV,hLowV,hStrictV⟩ :=
    exists_original_base_localization X h T x a hz ht f hf hLower
  let M₀ := weightedColumns α η
  let C₀ := contactOrbit a α B (rowProjector M₀)
  let F := actualProductGap X h T x (baseTimeStrictify f a) α (rowProjector M₀) θ
  have hM₀ : (M₀*M₀ᴴ).PosDef := by
    rw [show M₀*M₀ᴴ = B⁻¹ from hGram]
    exact hB.1.inv
  have hC₀ : IsCompact C₀ := isCompact_contactOrbit a α hα B (rowProjector M₀)
  have hC₀U : C₀ ⊆ productOpenDomain α V :=
    contactOrbit_subset_productOpenDomain a α B hB.1 (rowProjector M₀) V haV
  obtain ⟨O,hO,hC₀O,hOC,hOU⟩ := exists_open_precompact_between C₀
    (productOpenDomain α V) hC₀ (isOpen_productOpenDomain α V hV) hC₀U
  have hDom (Q : ProductPoint n m) (hQ : Q ∈ closure O) :
      Q.1 ∈ chartTarget x ∧ Q.2.1 ∈ Ioo 0 T := hVD (hOU hQ).1
  have hRank (Q : ProductPoint n m) (hQ : Q ∈ closure O) :
      (weightedColumns α Q.2.2*(weightedColumns α Q.2.2)ᴴ).PosDef :=
    (fullRankRect_iff_posDef _).mp (hOU hQ).2
  have hF0 : ∀ Q ∈ closure O, 0 ≤ F Q := by
    intro Q hQ
    obtain ⟨D,hD,hDMax⟩ := ((hoc T hT x).2 Q.1 Q.2.1 (hDom Q hQ).1 (hDom Q hQ).2).1.exists
    exact (actual_product_gap_support X h T x (baseTimeStrictify f a) α (fun i => (hα i).le)
      M₀ hM₀ θ hθ Q (hDom Q hQ).1 (hDom Q hQ).2 (hRank Q hQ)
      D hD hDMax (hLowV _ (hOU hQ).1)).1
  have hZero : ∀ Q ∈ closure O, F Q = 0 → Q ∈ C₀ := by
    intro Q hQ hFQ
    exact actual_product_gap_zero_orbit X h ρ hoc T hT x a B hB hMax
      (baseTimeStrictify f a) α (fun i => (hα i).le) M₀ hM₀ θ hθ Q
      (hDom Q hQ).1 (hDom Q hQ).2 (hRank Q hQ) (hLowV _ (hOU hQ).1)
      (hStrictV _ (hOU hQ).1) hFQ
  have hFLsc : LowerSemicontinuousOn F (closure O) :=
    actualProductGap_lowerSemicontinuousOn X h T x (baseTimeStrictify f a) α
      (fun i => (hα i).le) (rowProjector M₀) θ (closure O) hDom
      (fun Q hQ => hfV.contDiffAt (hV.mem_nhds (hOU hQ).1)) hRank
  obtain ⟨γ,hγ,hBoundary⟩ := exists_positive_frontier_gap O hO hOC F hFLsc hF0
    (fun Q hQ hFQ => hC₀O (hZero Q hQ hFQ))
  have hTuple : (a.1,a.2,η) ∈ C₀ := original_tuple_mem_contactOrbit a α η B hB.1 hGram
  have hfAt : baseTimeStrictify f a a = Real.log B.det.re :=
    (baseTimeStrictify_at f a).trans
      (hValue.trans (ellipsoidLogDet_eq_log_det_of_max X h T x a.1 a.2 B hB hMax))
  have hFAt : F (a.1,a.2,η) = 0 :=
    actual_product_gap_at_contacts X h T x a (baseTimeStrictify f a) α η B hB.1
      hGram hEnv hSum hfAt θ
  exact ⟨V,O,γ,hV,haV,hVD,hfV,hO,hC₀O,hOC,hOU,hC₀O hTuple,hγ,hBoundary,hFAt,hF0,hZero⟩

end Yau.NodeProofs.E02Aux

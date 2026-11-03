import Yau.Proofs.F05CompactCofinalClosure
import Yau.Proofs.F05CompactSolutionExtension
import Yau.Proofs.F05FiniteHorizonPrinciple

/-! Actual compact-domain solutions exist through every finite supplied
horizon. Local construction, cofinal closedness and strict right extension
are all proved inputs; no continuation or limiting-solver premise remains. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.Blueprint Yau.F05Transport
variable {n : ℕ} {X : KahlerManifold n}

theorem F05_flow_compact_finite_horizon (hn : 0 < n)
    {O : Set (Pt X)} {A : AtlasData X.manifold} (hA : GenuineAtlas O A)
    {χ : Fin A.count → Pt X → ℝ} (hχ : F05Partition O A χ)
    (o : Pt X) (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    (p : STF X) {S a : ℝ} (hS : 0 < S) (hp : SmoothSpaceTime p (Icc 0 S))
    (ha : 0 ≤ a) (hp0 : ∀ x ∈ closure O, p x 0 = a)
    (hpB : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 S, 0 ≤ p x t ∧ p x t ≤ ρ x t+2*a)
    (hCompat : ∀ x, derivWithin (p x) (Icc 0 S) 0 =
      Real.exp (-p x 0)*laplacian (h 0) (fun y => p y 0) x+
        (1-Real.exp (-p x 0))*scalarCurvature (h 0) x) :
    ∃ w : STF X, F05CompactDirichletSolution O A h p S w := by
  have hhS : MetricFamilySmooth h (Icc 0 S) := fun x j k =>
    (hloc.1.2.1 x j k).mono (fun z hz => ⟨hz.1,hz.2.1⟩)
  have hRS := F05_flow_scalar_smooth o h U P ρ hloc hS
  obtain ⟨δ,hδ,hδS,hLocal⟩ := F05_compact_dirichlet_local hA hχ h p hS hhS hp hRS hCompat
  let E := F05CompactAdmissibleTimes O A h p S
  have hPositive : ∃ t ∈ E, 0 < t := by
    obtain ⟨w,hw⟩ := hLocal δ hδ le_rfl
    exact ⟨δ,⟨hδ,hδS,w,hw⟩,hδ⟩
  have hUpper : ∀ t ∈ E, t ≤ S := fun t ht => ht.2.1
  have hClosed : ∀ T : ℝ, 0 < T → T ≤ S →
      (∀ ε : ℝ, 0 < ε → ∃ t ∈ E, T-ε < t ∧ t ≤ T) → T ∈ E := by
    intro T hT hTS hNear
    exact F05_flow_compact_admissible_closed hn hA hχ o h U P ρ hloc p hS hp ha hp0 hpB hT hTS hNear
  have hExtend : ∀ t ∈ E, t < S → ∃ T ∈ E, t < T := by
    intro t ht htS
    obtain ⟨w,hw⟩ := ht.2.2
    obtain ⟨T,v,htT,hTS,hv,hAgree⟩ := F05_compact_solution_extend hn hA hχ h p w ht.1 htS hhS hp hRS hw
    exact ⟨T,⟨ht.1.trans htT,hTS,v,hv⟩,htT⟩
  have hSAd : S ∈ E := F05_finite_horizon_principle hPositive hUpper hClosed hExtend
  exact hSAd.2.2

end Yau.Proofs.F05Aux

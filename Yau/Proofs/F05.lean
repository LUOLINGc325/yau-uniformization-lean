import spec.CHAIN.CONTRACTS
import Yau.Proofs.F05ActualExhaustionApproximants
import Yau.Proofs.F05ExhaustionLimitBarriers
import Yau.Proofs.F05ExhaustionLimitSmoothNear
import Yau.Proofs.F05IntrinsicLimitEquation
import Yau.Proofs.F05InitialContinuity

/-! The original F05 smooth majorant on the same arbitrary localized
flow. The actual smooth exhaustion, compatible compact-domain solutions,
uniform interior estimates, one global subsequence, nonlinear PDE,
positive-time smoothness and zero-initial continuity are all constructed. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.Blueprint Yau.F05Transport Yau.HeatConcreteBindings
variable {n : ℕ} {X : KahlerManifold n}

theorem F05_smooth_majorant (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) : SmoothMajorant X h ρ := by
  intro T hT v hVusc hVLocal hVRange hVisc
  obtain ⟨O,A,χ,δ,w,hO,hApprox⟩ := F05_flow_actual_exhaustion_approximants
    o h U P ρ hloc hT v hVusc hVLocal hVRange hVisc
  let p : ℕ → STF X := fun j =>
    flowCornerBoundary X ρ (F05ExhaustionError j) (δ j) F05PaperCornerCutoff
  have hA (j : ℕ) : GenuineAtlas (O j) (A j) := (hApprox j).1
  have hCompact (j : ℕ) (i : Fin (A j).count) :
      IsCompact (lift (A j) i '' Metric.closedBall 0 3) := (hApprox j).2.2.2.1 i
  have hp (j : ℕ) : SmoothSpaceTime (p j) (Icc 0 T) :=
    F05_flow_corner_smooth o h U P ρ hloc hT (F05ExhaustionError j) (δ j)
      F05PaperCornerCutoff F05PaperCornerCutoff_smooth
  have hw (j : ℕ) : F05CompactDirichletSolution (O j) (A j) h (p j) T (w j) :=
    (hApprox j).2.2.2.2.2.1
  have hBounds (j : ℕ) : ∀ x ∈ closure (O j), ∀ t ∈ Icc 0 T,
      0 ≤ w j x t ∧ w j x t ≤ ρ x t+2*F05ExhaustionError j :=
    (hApprox j).2.2.2.2.2.2.1
  have hComparison (j : ℕ) : ∀ x ∈ closure (O j), ∀ t ∈ Ico 0 T, v x t ≤ w j x t :=
    (hApprox j).2.2.2.2.2.2.2.2
  obtain ⟨φ,W,hφ,hW0,hPoint,hUniform⟩ := F05_flow_exhaustion_value_subsequence
    O hO A hA hCompact o h U P ρ hloc hT p w hp hw hBounds
  have hBarriers := F05_flow_exhaustion_limit_barriers
    O hO o h U P ρ hloc hT v hVRange w hBounds hComparison hφ W hW0 hPoint
  have hRange : ∀ x t, t ∈ Ico 0 T → 0 ≤ W x t ∧ W x t ≤ ρ x t :=
    fun x t ht => ⟨(hBarriers x t ht).1,(hBarriers x t ht).2.2⟩
  have hLimit := F05_flow_exhaustion_limit_equation
    O hO A hA hCompact o h U P ρ hloc hT p w hp hw hBounds hφ W hUniform
  have hNear := F05_flow_exhaustion_limit_smoothNear
    O hO A hA hCompact o h U P ρ hloc hT W hRange hLimit
  have hSmooth := F05_smoothNear_spacetime W hNear
  have hEquation := F05_exhaustion_limit_intrinsic_equation O hO A hA h W hSmooth
    (fun j i m => by
      obtain ⟨α,C,hα,hα1,hC,hSch,hEq⟩ := hLimit j i m
      exact hEq)
  obtain ⟨hInitial,hCont⟩ := F05_majorant_initial_continuity o h U P ρ hloc hT W hSmooth hRange
  refine ⟨W,hSmooth,hCont,hInitial,?_⟩
  intro x t ht
  exact ⟨(hBarriers x t ht).2.1,(hBarriers x t ht).2.2,fun htPos => hEquation x t ⟨htPos,ht.2⟩⟩

end Yau.Proofs.F05Aux

namespace Yau.Proofs

theorem F05 : Yau.BlueprintContracts.F05_contract := by
  intro n X o h U P ρ hloc
  exact F05Aux.F05_smooth_majorant o h U P ρ hloc

end Yau.Proofs

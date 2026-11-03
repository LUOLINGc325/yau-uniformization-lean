import Yau.Proofs.F05RawCompactUniformJets
import Yau.Proofs.F05ExhaustionContainment
import Yau.Proofs.F05CompactRhoBudget
import Yau.Proofs.F05ExhaustionApproximants

/-! Every fixed reference chart eventually has one actual common four-jet
budget along the genuine compact approximants. Only the fixed compact
rho profile is used; no global bound over the growing domains is needed. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.Blueprint Yau.F05Transport Yau.HeatConcreteBindings
variable {n : ℕ} {X : KahlerManifold n}

theorem F05_flow_exhaustion_uniform_jets (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
    (A : ℕ → AtlasData X.manifold) (hA : ∀ j, GenuineAtlas (O j) (A j))
    (hCompact : ∀ j i, IsCompact (lift (A j) i '' Metric.closedBall 0 3))
    (o : Pt X) (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    {T : ℝ} (hT : 0 < T) (p w : ℕ → STF X)
    (hp : ∀ j, SmoothSpaceTime (p j) (Icc 0 T))
    (hw : ∀ j, F05CompactDirichletSolution (O j) (A j) h (p j) T (w j))
    (hBounds : ∀ j, ∀ x ∈ closure (O j), ∀ t ∈ Icc 0 T,
      0 ≤ w j x t ∧ w j x t ≤ ρ x t+2*F05ExhaustionError j)
    (j : ℕ) (i : Fin (A j).count) {s : ℝ} (hs : 0 < s) (hsT : s < T) :
    ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 0 < C ∧ ∀ᶠ k in atTop,
      C2 (cylinder (region none (9/4)) s T) (pull (A j) i (w k)) ∧
      HolderBound α (cylinder (region none (9/4)) s T)
        (fun z => ((pull (A j) i (w k) z,spatialD (pull (A j) i (w k)) z),
          (spatialDD (pull (A j) i (w k)) z,
            timeD (cylinder (region none (9/4)) s T) (pull (A j) i (w k)) z))) C := by
  let K := lift (A j) i '' Metric.closedBall (0 : Space n) 3
  have hK : IsCompact K := hCompact j i
  obtain ⟨N,hN⟩ := F05_smooth_exhaustion_contains_compact hO hK
  obtain ⟨B,hB,hRho⟩ := F05_flow_compact_rho_budget o h U P ρ hloc T hK
  have hh : MetricFamilySmooth h (Icc 0 T) := fun x a b =>
    (hloc.1.2.1 x a b).mono (fun z hz => ⟨hz.1,hz.2.1⟩)
  have hR := F05_flow_scalar_smooth o h U P ρ hloc hT
  obtain ⟨α,C,hα,hα1,hC,hJets⟩ := F05_compact_solution_raw_uniform_jets
    (F03Aux.complexManifold_dimension_pos X.manifold) (hA j) i h hT hs hsT hB.le hh hR
  refine ⟨α,C,hα,hα1,hC,eventually_atTop.mpr ⟨N,?_⟩⟩
  intro k hk
  have hRawK (z : Space n) (hz : z ∈ Metric.ball 0 3) : lift (A j) i z ∈ K :=
    ⟨z,Metric.ball_subset_closedBall hz,rfl⟩
  have hDomain : lift (A j) i '' Metric.ball 0 3 ⊆ closure (O k) := by
    rintro x ⟨z,hz,rfl⟩
    exact subset_closure (hN k hk (hRawK z hz))
  apply hJets (O k) (A k) (hA k) (p k) (w k) (hp k) (hw k) hDomain
  intro z hz t ht
  have hzK := hRawK z hz
  have hBound := hBounds k (lift (A j) i z) (subset_closure (hN k hk hzK)) t ht
  refine ⟨hBound.1,?_⟩
  have hε := F05_exhaustion_error_le_one k
  linarith [hRho (lift (A j) i z) hzK t ht]

end Yau.Proofs.F05Aux

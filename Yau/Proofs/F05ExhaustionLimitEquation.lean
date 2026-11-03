import Yau.Proofs.F05ExhaustionValueCompactness
import Yau.Proofs.F05NativeJetRelativeSchauder
import Yau.Proofs.F05RelativeNonlinearRestriction

/-! Every actual uniform value limit of the genuine exhaustion subsequence
has the original nonlinear equation and a finite relative Schauder bound
on each full raw reference cylinder. The limiting jets are constructed
inside the finite native compactness theorem. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.Blueprint Yau.F05Transport Yau.HeatConcreteBindings
variable {n : ℕ} {X : KahlerManifold n}

theorem F05_flow_exhaustion_limit_equation (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
    (A : ℕ → AtlasData X.manifold) (hA : ∀ j, GenuineAtlas (O j) (A j))
    (hCompact : ∀ j i, IsCompact (lift (A j) i '' Metric.closedBall 0 3))
    (o : Pt X) (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    {T : ℝ} (hT : 0 < T) (p w : ℕ → STF X)
    (hp : ∀ j, SmoothSpaceTime (p j) (Icc 0 T))
    (hw : ∀ j, F05CompactDirichletSolution (O j) (A j) h (p j) T (w j))
    (hBounds : ∀ j, ∀ x ∈ closure (O j), ∀ t ∈ Icc 0 T,
      0 ≤ w j x t ∧ w j x t ≤ ρ x t+2*F05ExhaustionError j)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (W : STF X)
    (hLim : ∀ j (i : Fin (A j).count) m,
      TendstoUniformlyOn (fun k => pull (A j) i (w (φ k))) (pull (A j) i W) atTop
        (cylinder (region none (9/4)) (F05ExhaustionTime T m) T))
    (j : ℕ) (i : Fin (A j).count) (m : ℕ) :
    ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 0 < C ∧
      F05RelSchauder α (region none (9/4)) (Icc (F05ExhaustionTime T m) T) (pull (A j) i W) C ∧
      F05RelativeNonlinearEquation none (9/4) (F05ExhaustionTime T m) T
        (fun z => flatA (h z.2) (A j) i z) (fun z a => flatB (h z.2) (A j) i z a)
        (pull (A j) i (fun x t => scalarCurvature (h t) x)) (pull (A j) i W) := by
  let s := F05ExhaustionTime T m
  have hs : 0 < s := F05_exhaustion_time_pos hT m
  have hsT : s < T := F05_exhaustion_time_lt hT m
  obtain ⟨α,C,hα,hα1,hC,hJets⟩ := F05_flow_exhaustion_uniform_jets O hO A hA hCompact
    o h U P ρ hloc hT p w hp hw hBounds j i hs hsT
  have hRelative : ∀ᶠ k in atTop,
      F05RelSchauder α (region none (9/4)) (Icc s T) (pull (A j) i (w (φ k))) C :=
    (hφ.tendsto_atTop.eventually hJets).mono (fun k hk =>
      F05_relative_schauder_of_native_tuple (F05_region_uniqueDiffOn none (by norm_num)) hk.1 hk.2)
  have hh : MetricFamilySmooth h (Icc 0 T) := fun x a b =>
    (hloc.1.2.1 x a b).mono (fun z hz => ⟨hz.1,hz.2.1⟩)
  have hR := F05_flow_scalar_smooth o h U P ρ hloc hT
  obtain ⟨N,hN⟩ := F05_smooth_exhaustion_contains_compact hO (hCompact j i)
  have hEquation : ∀ᶠ k in atTop, F05RelativeNonlinearEquation none (9/4) s T
      (fun z => flatA (h z.2) (A j) i z) (fun z a => flatB (h z.2) (A j) i z a)
      (pull (A j) i (fun x t => scalarCurvature (h t) x)) (pull (A j) i (w k)) := by
    apply eventually_atTop.mpr
    refine ⟨N,?_⟩
    intro k hk
    have hDomain : lift (A j) i '' Metric.ball 0 3 ⊆ closure (O k) := by
      rintro x ⟨z,hz,rfl⟩
      exact subset_closure (hN k hk ⟨z,Metric.ball_subset_closedBall hz,rfl⟩)
    have hFull := F05_compact_solution_positive_smooth
      (F03Aux.complexManifold_dimension_pos X.manifold) (hA k) h (p k) (w k) hT hh (hp k) hR (hw k)
    have hRaw := F05_cross_atlas_raw_positive_smooth (hA j) (hA k) (w k) hs hsT i hDomain hFull
    have hLate := F05_compact_solution_late_equation (hA k) hs.le hsT (hw k)
    have hRawEquation := F05_raw_relative_nonlinear_equation (hA j) h
      (fun x t => scalarCurvature (h t) x) (w k) i hsT hDomain hRaw hLate
    have hDU : region (n := n) none (5/2) ⊆ Metric.ball 0 3 := by
      intro z hz
      rw [Metric.mem_ball,dist_zero_right]
      linarith [hz.1]
    have hC2 := F05_smooth_closed_slab_c2 Metric.isOpen_ball hDU hsT le_rfl hRaw
    exact F05_relative_nonlinear_equation_restrict none
      (by norm_num : (0 : ℝ) < 9/4) (by norm_num : (0 : ℝ) < 5/2) (by norm_num) hsT le_rfl le_rfl
      (F05_native_c2_to_relative (F05_region_uniqueDiffOn none (by norm_num)) hC2) hRawEquation
  obtain ⟨hSch,hEq⟩ := F05_eventual_nonlinear_relative_schauder_limit none
    (by norm_num : (0 : ℝ) < 9/4) hsT hα _ _ _ hRelative (hLim j i m)
    (hφ.tendsto_atTop.eventually hEquation)
  exact ⟨α,C,hα,hα1,hC,hSch,hEq⟩

end Yau.Proofs.F05Aux

import Yau.Proofs.F05ExhaustionLimitEquation
import Yau.Proofs.F05FlowRawLimitSmooth
import Yau.Proofs.F05SmoothNearTransport

/-! The actual nonlinear finite-Schauder reference limits and their rho
barrier imply genuine positive-time joint smoothness at every manifold
point. A strictly earlier terminal buffer avoids asserting regularity or
barriers at the original open final face. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.Blueprint Yau.F05Transport Yau.HeatConcreteBindings
variable {n : ℕ} {X : KahlerManifold n}

theorem F05_flow_exhaustion_limit_smoothNear (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
    (A : ℕ → AtlasData X.manifold) (hA : ∀ j, GenuineAtlas (O j) (A j))
    (hCompact : ∀ j i, IsCompact (lift (A j) i '' Metric.closedBall 0 3))
    (o : Pt X) (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    {T : ℝ} (hT : 0 < T) (W : STF X)
    (hRange : ∀ x t, t ∈ Ico 0 T → 0 ≤ W x t ∧ W x t ≤ ρ x t)
    (hLimit : ∀ j (i : Fin (A j).count) m,
      ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 0 < C ∧
        F05RelSchauder α (region none (9/4)) (Icc (F05ExhaustionTime T m) T) (pull (A j) i W) C ∧
        F05RelativeNonlinearEquation none (9/4) (F05ExhaustionTime T m) T
          (fun z => flatA (h z.2) (A j) i z) (fun z a => flatB (h z.2) (A j) i z a)
          (pull (A j) i (fun x t => scalarCurvature (h t) x)) (pull (A j) i W)) :
    ∀ x t, t ∈ Ioo 0 T → SmoothNear W x t := by
  intro x t ht
  have hxAll : x ∈ ⋃ j, O j := by rw [hO.2.2]; exact mem_univ x
  obtain ⟨j,hxj⟩ := mem_iUnion.mp hxAll
  obtain ⟨i,z,hz,hLift⟩ := mem_iUnion.mp ((hA j).2.1 (subset_closure hxj))
  let τ := t/2
  let S := (t+T)/2
  have hτ : 0 < τ := by dsimp only [τ]; linarith [ht.1]
  have hτt : τ < t := by dsimp only [τ]; linarith [ht.1]
  have htS : t < S := by dsimp only [S]; linarith [ht.2]
  have hST : S < T := by dsimp only [S]; linarith [ht.2]
  obtain ⟨m,hm⟩ := F05_exhaustion_time_cover T hτ
  let l := F05ExhaustionTime T m
  have hl : 0 < l := F05_exhaustion_time_pos hT m
  have hlS : l < S := hm.trans (hτt.trans htS)
  obtain ⟨α,C,hα,hα1,hC,hSch,hEq⟩ := hLimit j i m
  have hSmooth := F05_flow_raw_limit_smooth (hA j) i (hCompact j i)
    o h U P ρ hloc hT hl hm (hτt.trans htS) hST hα hα1 hC W hRange hSch hEq
  have hOpenSmooth : ContDiffOn ℝ ∞ (pull (A j) i W) (Metric.ball 0 (3/2) ×ˢ Ioo τ S) :=
    hSmooth.mono (fun q hq =>
      ⟨⟨(show ‖q.1‖ < 3/2 by simpa only [Metric.mem_ball,dist_zero_right] using hq.1).le,trivial⟩,
        Ioo_subset_Icc_self hq.2⟩)
  have hzBall : z ∈ Metric.ball (0 : Space n) (3/2) := by
    rw [Metric.mem_ball,dist_zero_right]
    linarith [hz.1]
  have hAt : ContDiffAt ℝ ∞ (pull (A j) i W) (z,t) := hOpenSmooth.contDiffAt
    ((Metric.isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨hzBall,hτt,htS⟩)
  have hNear := F05_flat_smoothNear_to_manifold (z := z) (t := t) (hA j) i W
    (Metric.ball_subset_ball (by norm_num : (3/2 : ℝ) ≤ 3) hzBall) hAt
  rwa [hLift] at hNear

end Yau.Proofs.F05Aux

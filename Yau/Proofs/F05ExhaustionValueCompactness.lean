import Yau.Proofs.F05ExhaustionUniformJets
import Yau.Proofs.F05ExhaustionTime
import Yau.Proofs.F05CountableJetSubsequence

/-! One genuine subsequence converges uniformly on every fixed countable
reference cylinder. Its scalar limits agree on all overlaps because they
are limits of the same original manifold sequence; a single actual
manifold function is constructed by limUnder. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.Blueprint Yau.F05Transport Yau.HeatConcreteBindings Yau.LeafProofs.L16Aux
variable {n : ℕ} {X : KahlerManifold n}

theorem F05_flow_exhaustion_value_subsequence (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
    (A : ℕ → AtlasData X.manifold) (hA : ∀ j, GenuineAtlas (O j) (A j))
    (hCompact : ∀ j i, IsCompact (lift (A j) i '' Metric.closedBall 0 3))
    (o : Pt X) (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    {T : ℝ} (hT : 0 < T) (p w : ℕ → STF X)
    (hp : ∀ j, SmoothSpaceTime (p j) (Icc 0 T))
    (hw : ∀ j, F05CompactDirichletSolution (O j) (A j) h (p j) T (w j))
    (hBounds : ∀ j, ∀ x ∈ closure (O j), ∀ t ∈ Icc 0 T,
      0 ≤ w j x t ∧ w j x t ≤ ρ x t+2*F05ExhaustionError j) :
    ∃ (φ : ℕ → ℕ) (W : STF X), StrictMono φ ∧ (∀ x, W x 0 = 0) ∧
      (∀ x t, t ∈ Ioc 0 T → Tendsto (fun k => w (φ k) x t) atTop (𝓝 (W x t))) ∧
      ∀ j (i : Fin (A j).count) m,
        TendstoUniformlyOn (fun k => pull (A j) i (w (φ k))) (pull (A j) i W) atTop
          (cylinder (region none (9/4)) (F05ExhaustionTime T m) T) := by
  classical
  let I := (Σ j : ℕ, Fin (A j).count) × ℕ
  letI : Countable I := inferInstanceAs (Countable ((Σ j : ℕ, Fin (A j).count) × ℕ))
  let Q : I → Set (Point n) := fun a =>
    cylinder (region none (9/4)) (F05ExhaustionTime T a.2) T
  let f : ℕ → I → Point n → ℝ := fun k a => pull (A a.1.1) a.1.2 (w k)
  have hFamily (a : I) := F05_flow_exhaustion_uniform_jets O hO A hA hCompact
    o h U P ρ hloc hT p w hp hw hBounds a.1.1 a.1.2
    (F05_exhaustion_time_pos hT a.2) (F05_exhaustion_time_lt hT a.2)
  choose α C hα hα1 hC hJets using hFamily
  have hf (a : I) : ∀ᶠ k in atTop, HolderBound (α a) (Q a) (f k a) (C a) :=
    (hJets a).mono (fun k hk => holderBound_fst (holderBound_fst hk.2))
  have hQ (a : I) : IsCompact (Q a) := (F05_region_isCompact none (9/4)).prod isCompact_Icc
  obtain ⟨φ,g,hφ,hg⟩ := F05_countable_eventual_holder_subsequence Q hQ α C hα f hf
  let W : STF X := fun x t => if 0 < t then limUnder atTop (fun k => w (φ k) x t) else 0
  have hPoint : ∀ x t, t ∈ Ioc 0 T → Tendsto (fun k => w (φ k) x t) atTop (𝓝 (W x t)) := by
    intro x t ht
    have hxAll : x ∈ ⋃ j, O j := by rw [hO.2.2]; exact mem_univ x
    obtain ⟨j,hxj⟩ := mem_iUnion.mp hxAll
    obtain ⟨i,z,hz,hzx⟩ := F05_cover (hA j) (subset_closure hxj)
    obtain ⟨m,hm⟩ := F05_exhaustion_time_cover T ht.1
    let a : I := (⟨j,i⟩,m)
    have hzQ : (z,t) ∈ Q a := by
      refine ⟨⟨?_,trivial⟩,hm.le,ht.2⟩
      linarith [hz.1]
    have hValue := (hg a).tendsto_at hzQ
    change Tendsto (fun k => w (φ k) (lift (A j) i z) t) atTop (𝓝 (g a (z,t))) at hValue
    rw [hzx] at hValue
    change Tendsto (fun k => w (φ k) x t) atTop
      (𝓝 (if 0 < t then limUnder atTop (fun k => w (φ k) x t) else 0))
    rw [if_pos ht.1]
    exact tendsto_nhds_limUnder ⟨g a (z,t),hValue⟩
  refine ⟨φ,W,hφ,fun x => by simp only [W,lt_self_iff_false,if_false],hPoint,?_⟩
  intro j i m
  let a : I := (⟨j,i⟩,m)
  change TendstoUniformlyOn (fun k => f (φ k) a) (pull (A j) i W) atTop (Q a)
  apply (hg a).congr_right
  intro z hz
  have hRaw := (hg a).tendsto_at hz
  have ht : z.2 ∈ Ioc 0 T := ⟨(F05_exhaustion_time_pos hT m).trans_le hz.2.1,hz.2.2⟩
  have hWPoint := hPoint (lift (A j) i z.1) z.2 ht
  exact tendsto_nhds_unique hRaw hWPoint

end Yau.Proofs.F05Aux

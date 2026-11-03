import Yau.Proofs.C05LoopIngressSquare
import Yau.Proofs.C07PolygonalPrefix

/-! A compact parameter cover gives one original-metric curve-length bound for the continuous loop. -/
noncomputable section
open scoped Topology Manifold unitInterval
namespace Yau.Proofs.C05LoopIngressAux
open Yau Set
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 1200000

theorem exists_uniform_loop_curve_family (g : SmoothMetric M) (hg : MetricSmooth g.form)
    (o x : M.Carrier) (γ : Path x x) :
    ∃ K : Set M.Carrier, ∃ L : ℝ, IsCompact K ∧ 0 ≤ L ∧
      ∀ u : I, ∃ η : IntegrableCurve g.form o (γ u),
        curveLength g.form η.1 ≤ L ∧ ∀ s ∈ Icc (0 : ℝ) 1, η.1 s ∈ K := by
  classical
  obtain ⟨δ⟩ := g.curve_nonempty o x
  let δpath : Path o x :=
    { toFun := fun u => δ u
      continuous_toFun := δ.continuous_on.comp_continuous continuous_subtype_val (fun u => u.2)
      source' := δ.start_eq
      target' := δ.finish_eq }
  obtain ⟨H, hH0, hH1⟩ := exists_based_square_ending_loop δpath γ
  have hlocal : ∀ u₀ : I, ∃ N : Set I, IsOpen N ∧ u₀ ∈ N ∧
      ∃ K : Set M.Carrier, ∃ L : ℝ, IsCompact K ∧ 0 ≤ L ∧
        ∀ u ∈ N, ∃ η : IntegrableCurve g.form o (γ u),
          curveLength g.form η.1 ≤ L ∧ ∀ s ∈ Icc (0 : ℝ) 1, η.1 s ∈ K := by
    intro u₀
    obtain ⟨N, hN, huN, K, L, hK, hL, Γ, _, _, hlen, himage, _⟩ :=
      C07PolygonalPrefixAux.exists_local_polygonal_prefix hg o H hH0 u₀
    refine ⟨N, hN, huN, K, L, hK, hL, ?_⟩
    intro u hu
    let a : I × N := (1, ⟨u, hu⟩)
    let η := C07PolygonalPrefixAux.repointCurve (Γ a) rfl (hH1 u)
    refine ⟨η, ?_, ?_⟩
    · exact hlen a
    · exact himage a
  choose N hN huN K L hK hL hpaths using hlocal
  have hcover : (univ : Set I) ⊆ ⋃ u, N u := by
    intro u _
    exact mem_iUnion.mpr ⟨u, huN u⟩
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover N hN hcover
  let bigK : Set M.Carrier := ⋃ u : S, K u
  refine ⟨bigK, ∑ u ∈ S, L u, isCompact_iUnion (fun u : S => hK u),
    Finset.sum_nonneg (fun u _ => hL u), ?_⟩
  intro u
  obtain ⟨v, hv⟩ := mem_iUnion.mp (hS (mem_univ u))
  obtain ⟨hvS, huv⟩ := mem_iUnion.mp hv
  obtain ⟨η, hηlen, hηimage⟩ := hpaths v u huv
  refine ⟨η, hηlen.trans (Finset.single_le_sum (fun j _ => hL j) hvS), ?_⟩
  intro s hs
  exact subset_iUnion (fun v : S => K v) ⟨v, hvS⟩ (hηimage s hs)

end Yau.Proofs.C05LoopIngressAux

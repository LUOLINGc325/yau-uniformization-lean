import Yau.Proofs.C07ChartBallLiftFamily
import Yau.Proofs.C07BranchMonodromy
import Yau.Proofs.C07BranchContinuation
import Yau.Proofs.C07OpenBranchGlue
import Yau.Proofs.C07FiniteDecay

/-! Actual local chart lifts glue to one exponentially small inverse near any compact set. -/

open scoped Manifold Topology

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint Set Yau.Proofs.D04AtlasGlueAux

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P ρ : STF X}

set_option maxHeartbeats 1200000 in
theorem eventually_inverse_near_compact
    (hflow : FlowStage X o h U P ρ) (hwindow : RicciWindows X o h ρ)
    (hsimply : SimplyConnectedSpace (Pt X))
    {r c C t₀ : ℝ} (hr : 0 < r) (hc : 0 < c)
    (Φ : ℝ → ComplexVector n → Pt X)
    (hcharts : ∀ t, t₀ ≤ t → UnitaryChart (h t) o (Φ t) r c C)
    {K : Set (Pt X)} (hK : IsCompact K) :
    ∃ (V : Set (Pt X)) (b : ℝ → Pt X → ComplexVector n) (a A T : ℝ),
      IsOpen V ∧ K ⊆ V ∧ o ∈ V ∧ 0 < a ∧ 0 ≤ A ∧ t₀ ≤ T ∧
      ∀ t, T ≤ t → ContinuousOn (b t) V ∧
        MDifferentiableOn (ComplexModel n) 𝓘(ℂ, ComplexVector n) (b t) V ∧ b t o = 0 ∧
        ∀ x ∈ V, b t x ∈ Metric.ball 0 r ∧ Φ t (b t x) = x ∧
          ‖b t x‖ ≤ A * Real.exp (-a * ρ o t) := by
  classical
  obtain ⟨balls, hballs⟩ := exists_countable_chartBalls X.manifold
  obtain ⟨J, hcover⟩ := finite_chartBall_cover balls hballs (hK.union isCompact_singleton)
  let B : J → ChartBall X.manifold := fun i => balls i.1
  let V : Set (Pt X) := ⋃ i : J, (B i).inner
  have hcover' : K ∪ {o} ⊆ V := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  have ho : o ∈ V := hcover' (Or.inr (mem_singleton o))
  obtain ⟨i₀, hi₀⟩ := mem_iUnion.mp ho
  choose γ a A T E ha hA hT hE using
    (fun i : J => exists_chartBall_lift_family hflow hwindow hr hc Φ hcharts (B i))
  let b : J → ℝ → Pt X → ComplexVector n := fun i t => chartBallLiftEnd (B i) (E i t)
  let Tbase := max t₀ (∑ i : J, max 0 (T i))
  have htbase : t₀ ≤ Tbase := le_max_left _ _
  have hTbase (i : J) : T i ≤ Tbase :=
    (le_max_right 0 (T i)).trans
      ((Finset.single_le_sum (fun j _ => le_max_left 0 (T j)) (Finset.mem_univ i)).trans
        (le_max_right _ _))
  have hbc (i : J) (t : ℝ) (ht : Tbase ≤ t) : ContinuousOn (b i t) (B i).outer :=
    chartBallLiftEnd_continuousOn (B i) (E i t) (hE i t ((hTbase i).trans ht)).1
  have hbp (i : J) (t : ℝ) (ht : Tbase ≤ t) (x : Pt X) (hx : x ∈ (B i).outer) :
      b i t x ∈ Metric.ball 0 r ∧ Φ t (b i t x) = x :=
    chartBallLiftEnd_point (B i) (γ i) (E i t)
      (hE i t ((hTbase i).trans ht)).2.2.1 hx
  have hpair (i j : J) : ∃ S : ℝ, Tbase ≤ S ∧ ∀ t, S ≤ t →
      EqOn (b i t) (b j t) ((B i).core ∩ (B j).core) := by
    apply uniform_eventual_branch_agreement (B i).isOpen_outer (B j).isOpen_outer
      ((B i).isCompact_core.inter_right (B j).isCompact_core.isClosed)
      (fun x hx => ⟨(B i).core_subset_outer hx.1, (B j).core_subset_outer hx.2⟩)
      Φ (b i) (b j) (fun t ht => (hcharts t (htbase.trans ht)).1)
      (hbc i) (hbc j)
      (fun t ht x hx => (hbp i t ht x hx).1)
      (fun t ht x hx => (hbp j t ht x hx).1)
      (fun t ht x hx => (hbp i t ht x hx.1).2.trans (hbp j t ht x hx.2).2.symm)
    intro x hx
    exact eventually_chartBall_endpoint_agreement hflow hwindow hsimply hr hc Φ hcharts
      (B i) (B j) (γ i) (γ j) (E i) (E j) (T i) (T j)
      (fun t ht => ⟨(hE i t ht).1, (hE i t ht).2.1, (hE i t ht).2.2.1⟩)
      (fun t ht => ⟨(hE j t ht).1, (hE j t ht).2.1, (hE j t ht).2.2.1⟩) hx.1 hx.2
  choose S hSbase hS using hpair
  let Tpair := max Tbase (∑ p : J × J, max 0 (S p.1 p.2))
  have hpairbase : Tbase ≤ Tpair := le_max_left _ _
  have hSpair (i j : J) : S i j ≤ Tpair :=
    (le_max_right 0 (S i j)).trans
      ((Finset.single_le_sum (fun p _ => le_max_left 0 (S p.1 p.2))
        (Finset.mem_univ (i, j))).trans (le_max_right _ _))
  have hagree (t : ℝ) (ht : Tpair ≤ t) (i j : J) (x : Pt X)
      (hxi : x ∈ (B i).inner) (hxj : x ∈ (B j).inner) : b i t x = b j t x :=
    hS i j t ((hSpair i j).trans ht)
      ⟨(B i).inner_subset_core hxi, (B j).inner_subset_core hxj⟩
  have hoi₀ : o ∈ (B i₀).outer := (B i₀).core_subset_outer ((B i₀).inner_subset_core hi₀)
  obtain ⟨Szero, _, hzero⟩ := eventually_based_loop_lift_zero hflow hwindow hsimply hr hc
    Φ hcharts (γ i₀ ⟨o, hoi₀⟩).1
  obtain ⟨α, D, Sdecay, hα, hD, hdecay⟩ := finite_uniform_exponential_bound Finset.univ
    (ρ o) hwindow.2.2.1 (fun i : J => (B i).inner) b a A T
    (fun i _ => ha i) (fun i _ => hA i) (by
      intro i _ t ht x hx
      have hxo := (B i).core_subset_outer ((B i).inner_subset_core hx)
      change ‖chartBallLiftEnd (B i) (E i t) x‖ ≤ _
      rw [chartBallLiftEnd_eq (B i) (E i t) hxo]
      exact (hE i t ht).2.2.2 _)
  let Tfinal := max Tpair (max Szero Sdecay)
  let f : ℝ → Pt X → ComplexVector n := fun t => openBranchGlue (fun i => (B i).inner) (fun i => b i t)
  refine ⟨V, f, α, D, Tfinal, isOpen_iUnion (fun i => (B i).isOpen_inner),
    fun x hx => hcover' (Or.inl hx), ho, hα, hD,
    htbase.trans (hpairbase.trans (le_max_left _ _)), ?_⟩
  intro t ht
  have htp : Tpair ≤ t := (le_max_left _ _).trans ht
  have htb : Tbase ≤ t := hpairbase.trans htp
  have htz : Szero ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have htd : Sdecay ≤ t := (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  have hbci (i : J) : ContinuousOn (b i t) (B i).inner :=
    (hbc i t htb).mono ((B i).inner_subset_core.trans (B i).core_subset_outer)
  have hbpi (i : J) (x : Pt X) (hx : x ∈ (B i).inner) :
      b i t x ∈ Metric.ball 0 r ∧ Φ t (b i t x) = x :=
    hbp i t htb x ((B i).core_subset_outer ((B i).inner_subset_core hx))
  have hfzero : f t o = 0 := by
    rw [show f t o = b i₀ t o from openBranchGlue_eq _ _ (hagree t htp) hi₀]
    change chartBallLiftEnd (B i₀) (E i₀ t) o = 0
    rw [chartBallLiftEnd_eq (B i₀) (E i₀ t) hoi₀]
    have he := hE i₀ t ((hTbase i₀).trans htb)
    exact hzero t htz (fun u => E i₀ t (u, ⟨o, hoi₀⟩))
      (he.1.comp (continuous_id.prodMk continuous_const))
      (fun u => (he.2.2.1 (u, ⟨o, hoi₀⟩)).1)
      (fun u => (he.2.2.1 (u, ⟨o, hoi₀⟩)).2) (he.2.1 _)
  refine ⟨openBranchGlue_continuousOn _ _ (fun i => (B i).isOpen_inner) hbci (hagree t htp),
    openBranchGlue_mdifferentiable _ _ (fun i => (B i).isOpen_inner) hbci (hagree t htp)
      (hcharts t (htbase.trans htb)).1 hbpi, hfzero, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  have hfx : f t x = b i t x := openBranchGlue_eq _ _ (hagree t htp) hi
  rw [hfx]
  exact ⟨(hbpi i x hi).1, (hbpi i x hi).2, hdecay t htd i (Finset.mem_univ _) x hi⟩

end Yau.Proofs.C07Aux

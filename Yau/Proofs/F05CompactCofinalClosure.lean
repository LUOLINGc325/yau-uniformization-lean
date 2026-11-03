import Yau.Proofs.F05CofinalLateSolution
import Yau.Proofs.F05CofinalReflectionTimes
import Yau.Proofs.F05CompactCoherentLimit
import Yau.Proofs.F05CompactLatePaste
import Yau.Proofs.F05CompactFlowUniformBounds

/-! The actual compact-domain admissible times contain every positive
cofinal endpoint. The uniform flow estimate, fixed-cylinder jet limit,
original PDE and early trace matching are all discharged internally. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.Blueprint Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {X : KahlerManifold n}

def F05CompactAdmissibleTimes (O : Set (Pt X)) (A : AtlasData X.manifold)
    (h : Flow X) (p : STF X) (S : ℝ) : Set ℝ :=
  {t | 0 < t ∧ t ≤ S ∧ ∃ w : STF X, F05CompactDirichletSolution O A h p t w}

theorem F05_flow_compact_admissible_closed (hn : 0 < n)
    {O : Set (Pt X)} {A : AtlasData X.manifold} (hA : GenuineAtlas O A)
    {χ : Fin A.count → Pt X → ℝ} (hχ : F05Partition O A χ)
    (o : Pt X) (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    (p : STF X) {S a T : ℝ} (hS : 0 < S) (hp : SmoothSpaceTime p (Icc 0 S))
    (ha : 0 ≤ a) (hp0 : ∀ x ∈ closure O, p x 0 = a)
    (hpB : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 S, 0 ≤ p x t ∧ p x t ≤ ρ x t+2*a)
    (hT : 0 < T) (hTS : T ≤ S)
    (hNear : ∀ ε : ℝ, 0 < ε →
      ∃ t ∈ F05CompactAdmissibleTimes O A h p S, T-ε < t ∧ t ≤ T) :
    T ∈ F05CompactAdmissibleTimes O A h p S := by
  let E := F05CompactAdmissibleTimes O A h p S
  change T ∈ E
  by_cases hMem : T ∈ E
  · exact hMem
  obtain ⟨t₀,ht₀E,hNear₀,ht₀T⟩ := hNear (T/2) (by positivity)
  have ht₀Ad : 0 < t₀ ∧ t₀ ≤ S ∧ ∃ u : STF X, F05CompactDirichletSolution O A h p t₀ u := ht₀E
  have ht₀ : 0 < t₀ := ht₀Ad.1
  have ht₀T' : t₀ < T := lt_of_le_of_ne ht₀T (by
    intro hEq
    exact hMem (hEq ▸ ht₀E))
  obtain ⟨u₀,hu₀⟩ := ht₀Ad.2.2
  let s := t₀/8
  let r := t₀/2
  let b := min s 1
  have hs : 0 < s := by dsimp only [s]; positivity
  have hr : 0 < r := by dsimp only [r]; positivity
  have hst₀ : s < t₀ := by dsimp only [s]; linarith
  have hrt₀ : r < t₀ := by dsimp only [r]; linarith
  have hsr : s < r := by dsimp only [s,r]; linarith
  have hb : 0 < b := lt_min hs (by norm_num)
  have hb1 : b ≤ 1 := min_le_right _ _
  have hbs : b ≤ s := min_le_left _ _
  have hsrs : s ≤ r-s := by dsimp only [s,r]; linarith
  have hbr : b/2 ≤ r-s := by linarith
  have hsS : s < S := hst₀.trans_le ht₀Ad.2.1
  obtain ⟨γ,C,hγ,hγ1,hC,hEstimate⟩ := F05_compact_flow_uniform_positive_schauder (a := a)
    hn hA hχ o h U P ρ hloc p hS hp hs hsS ha hp0 hpB
  obtain ⟨τ,hτConv,hτAll⟩ := F05_cofinal_reflection_times (E := E) hst₀ ht₀T' hMem hNear
  have hτAd (k : ℕ) : 0 < τ k ∧ τ k ≤ S ∧
      ∃ w : STF X, F05CompactDirichletSolution O A h p (τ k) w := (hτAll k).1
  choose w hw using fun k => (hτAd k).2.2
  have hRelative (k : ℕ) (i : Fin A.count) :
      F05RelSchauder γ (F05D A i) (Icc s (τ k)) (pull A i (w k)) C :=
    hEstimate (τ k) (hst₀.trans (hτAll k).2.1) (hτAd k).2.1 (w k) (hw k) i
  have hhS : MetricFamilySmooth h (Icc 0 S) := fun x j k =>
    (hloc.1.2.1 x j k).mono (fun z hz => ⟨hz.1,hz.2.1⟩)
  have hRS := F05_flow_scalar_smooth o h U P ρ hloc hS
  have hSub : Icc (0 : ℝ) T ⊆ Icc 0 S := Icc_subset_Icc le_rfl hTS
  have hhT : MetricFamilySmooth h (Icc 0 T) := fun x j k => (hhS x j k).mono (prod_mono subset_rfl hSub)
  have hpT : SmoothSpaceTime p (Icc 0 T) := fun x => (hp x).mono (prod_mono subset_rfl hSub)
  have hRT : SmoothSpaceTime (fun x t => scalarCurvature (h t) x) (Icc 0 T) :=
    fun x => (hRS x).mono (prod_mono subset_rfl hSub)
  obtain ⟨φ,W,K,hφ,hK,hW,hWCont,hWBoundary,hWEquation,hWConv⟩ := F05_cofinal_late_solution hA hχ h p
    hT hs hb hb1 hsr hbr hγ hγ1 hC.le hhT hpT hRT τ w hτConv
    (fun k => hrt₀.trans (hτAll k).2.1) (fun k => (hτAll k).2.2.1)
    (fun k => (hτAll k).2.2.2) hw hRelative
  have hTraceLimit := F05_compact_coherent_limit_eq hA h p u₀ W hr.le ht₀ hhS hRS hu₀
    (fun k => τ (φ k)) (fun k => w (φ k)) (fun k => (hτAll (φ k)).2.1.le)
    (fun k => (hτAd (φ k)).2.1) (fun k => hw (φ k))
    (fun x hx t ht => hWConv x hx t ⟨ht.1,ht.2.trans_lt ht₀T'⟩)
  have hTrace (x : Pt X) (hx : x ∈ closure O) : u₀ x r = W x r :=
    (hTraceLimit x hx r ⟨le_rfl,hrt₀.le⟩).symm
  obtain ⟨v,hv,hOld⟩ := F05_compact_solution_of_late_solution hA h p u₀ W hr hrt₀.le
    (hrt₀.trans ht₀T') hu₀ (by positivity : (0 : ℝ) < γ/2) hK hW hWCont hWBoundary hWEquation hTrace
  exact ⟨hT,hTS,v,hv⟩

end Yau.Proofs.F05Aux

import Yau.Proofs.F05CompactFiniteHorizon
import Yau.Proofs.F05CornerBounds
import Yau.Proofs.F05SchauderViscosityComparison

/-! The paper's actual corrected corner datum gives full finite-horizon
compact approximants, their original flow barriers and viscosity
comparison for every supplied original subsolution. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.Blueprint Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {X : KahlerManifold n}

def F05PaperCornerCutoff (t : ℝ) : ℝ := 1-initialTimeCutoff 1 t

theorem F05PaperCornerCutoff_smooth : ContDiff ℝ ∞ F05PaperCornerCutoff :=
  contDiff_const.sub (initialTimeCutoff_contDiff 1)

theorem F05PaperCornerCutoff_range (t : ℝ) : 0 ≤ F05PaperCornerCutoff t ∧ F05PaperCornerCutoff t ≤ 1 := by
  have h := initialTimeCutoff_mem_Icc 1 t
  dsimp only [F05PaperCornerCutoff]
  constructor <;> linarith [h.1,h.2]

theorem F05PaperCornerCutoff_germ : F05PaperCornerCutoff =ᶠ[𝓝 0] (fun _ => 1) := by
  filter_upwards [F05_initialTimeCutoff_zero_germ (by norm_num : (0 : ℝ) < 1)] with t ht
  simp only [F05PaperCornerCutoff,ht,sub_zero]

theorem F05PaperCornerCutoff_support (t : ℝ) (ht : 1 ≤ t) : F05PaperCornerCutoff t = 0 := by
  simp only [F05PaperCornerCutoff,initialTimeCutoff_eq_one (by norm_num : (0 : ℝ) < 1)
    (show (1 : ℝ)/2 ≤ t by linarith),sub_self]

theorem F05_flow_finite_horizon_approximant (hn : 0 < n)
    {O : Set (Pt X)} {A : AtlasData X.manifold} (hA : GenuineAtlas O A)
    {χ : Fin A.count → Pt X → ℝ} (hχ : F05Partition O A χ)
    (o : Pt X) (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    {T S a : ℝ} (hS : 0 < S) (hST : S ≤ T) (ha : 0 < a) (v : STF X)
    (hVusc : UpperSemicontinuousOn (fun z : Pt X × ℝ => v z.1 z.2) (univ ×ˢ Icc 0 T))
    (hVLocal : ∀ K : Set (Pt X), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ t ∈ Icc 0 T, |v x t| ≤ C)
    (hVRange : ∀ x t, t ∈ Icc 0 T → 0 ≤ v x t ∧ v x t ≤ ρ x t)
    (hVisc : NonlinearViscositySub h T v) :
    ∃ (δ : ℝ) (w : STF X), 0 < δ ∧
      F05CompactDirichletSolution O A h (flowCornerBoundary X ρ a δ F05PaperCornerCutoff) S w ∧
      (∀ x ∈ closure O, ∀ t ∈ Icc 0 S, 0 ≤ w x t ∧ w x t ≤ ρ x t+2*a) ∧
      (∀ x ∈ frontier O, ∀ t ∈ Icc 0 S, ρ x t+a/2 ≤ w x t ∧ w x t ≤ ρ x t+a) ∧
      (∀ s : ℝ, 0 < s → s < S → ∀ i,
        ContDiffOn ℝ ∞ (pull A i w) (F05D A i ×ˢ Icc s S)) ∧
      ∀ x ∈ closure O, ∀ t ∈ Ico 0 S, v x t ≤ w x t := by
  obtain ⟨δ,hδ,hData⟩ := F05_flow_corner_uniform_bounds hA o h U P ρ hloc ha
  let p := flowCornerBoundary X ρ a δ F05PaperCornerCutoff
  have hp : SmoothSpaceTime p (Icc 0 S) :=
    F05_flow_corner_smooth o h U P ρ hloc hS a δ F05PaperCornerCutoff F05PaperCornerCutoff_smooth
  have hp0 (x : Pt X) : p x 0 = a :=
    flowCornerBoundary_initial o h U P ρ hloc a δ F05PaperCornerCutoff x
  have hpBoundary (x : Pt X) (hx : x ∈ frontier O) (t : ℝ) (ht : t ∈ Icc 0 S) :
      ρ x t+a/2 ≤ p x t ∧ p x t ≤ ρ x t+a :=
    hData F05PaperCornerCutoff F05PaperCornerCutoff_range F05PaperCornerCutoff_support
      x (frontier_subset_closure hx) t ht.1
  have hpB (x : Pt X) (hx : x ∈ frontier O) (t : ℝ) (ht : t ∈ Icc 0 S) :
      0 ≤ p x t ∧ p x t ≤ ρ x t+2*a := by
    have hB := hpBoundary x hx t ht
    have hρ := Yau.F04Proof.rho_nonneg o h U P ρ hloc x t ht.1
    constructor <;> linarith
  have hCompat (x : Pt X) : derivWithin (p x) (Icc 0 S) 0 =
      Real.exp (-p x 0)*laplacian (h 0) (fun y => p y 0) x+
        (1-Real.exp (-p x 0))*scalarCurvature (h 0) x := by
    have hTime := ((flowCornerBoundary_initial_derivative o h U P ρ hloc a δ F05PaperCornerCutoff
      F05PaperCornerCutoff_germ x).mono
      (show Icc (0 : ℝ) S ⊆ Ici 0 from fun t ht => ht.1)).derivWithin
      (uniqueDiffOn_Icc hS 0 ⟨le_rfl,hS.le⟩)
    rw [show (fun y => p y 0) = (fun _ => a) from funext hp0,
      Yau.LeafProofs.L18Aux.laplacian_const,hp0 x,mul_zero,zero_add]
    simpa only [hloc.1.1] using hTime
  obtain ⟨w,hw⟩ := F05_flow_compact_finite_horizon hn hA hχ o h U P ρ hloc p hS hp ha.le
    (fun x _ => hp0 x) hpB hCompat
  have hBounds := F05_compact_flow_barriers hA o h U P ρ hloc p w hS le_rfl ha.le
    (fun x _ => hp0 x) hpB hw
  have hhS : MetricFamilySmooth h (Icc 0 S) := fun x j k =>
    (hloc.1.2.1 x j k).mono (fun z hz => ⟨hz.1,hz.2.1⟩)
  have hRS := F05_flow_scalar_smooth o h U P ρ hloc hS
  have hSmooth := F05_compact_solution_positive_smooth hn hA h p w hS hhS hp hRS hw
  have hwOriginal := hw
  obtain ⟨β,K,hβ,hβ1,hK,hSch,hCont,h0,hBoundary,hEq⟩ := hw
  have hLat (x : Pt X) (hx : x ∈ frontier O) (t : ℝ) (ht : t ∈ Icc 0 S) :
      ρ x t+a/2 ≤ w x t ∧ w x t ≤ ρ x t+a := by
    rw [hBoundary x hx t ht]
    exact hpBoundary x hx t ht
  have hComparison := F05_flow_schauder_viscosity_comparison hn hA o h U P ρ hloc hS hST hβ hβ1
    v w p hVusc hVLocal hVRange hVisc hp hCont hSch (fun x hx t ht => (hBounds x hx t ht).1)
    h0 hBoundary (fun x hx t ht => by linarith [(hLat x hx t ht).1]) hEq
  exact ⟨δ,w,hδ,hwOriginal,hBounds,hLat,hSmooth,hComparison⟩

end Yau.Proofs.F05Aux

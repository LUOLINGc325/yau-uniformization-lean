import Yau.Proofs.F05LocalAtlas
import Yau.Proofs.F05AtlasModel

/-! Compactness constructs the actual finite buffered atlas from the original
smooth-domain predicate, with all-order bounds on the computed chart functions. -/

open Set
open scoped Topology ContDiff Manifold
noncomputable section
set_option maxHeartbeats 2000000

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.HeatConcreteBindings Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_finite_buffered_atlas_core (hn : 0 < n) (O : Set M.Carrier)
    (hO : SmoothPrecompactDomain O) :
    ∃ A : AtlasData M, GenuineAtlas O A ∧
      closure O ⊆ ⋃ i, lift A i '' region (A.normal i) (1/8) := by
  classical
  let K := closure O
  choose x ν c hChart using
    (fun p : K => smoothPrecompact_physical_chart hO p.val p.property)
  let e : K → OpenPartialHomeomorph M.Carrier (Space n) :=
    fun p => (chartAt (Space n) (x p)).trans (c p)
  let U : K → Set M.Carrier := fun p => (e p).source ∩ (e p) ⁻¹' Metric.ball 0 (1/8)
  have hUopen (p : K) : IsOpen (U p) := (e p).isOpen_inter_preimage Metric.isOpen_ball
  have hpU (p : K) : p.val ∈ U p := by
    obtain ⟨hpChart,hpSource,hpZero,hSource,hBuffer,hSmooth,hInverse,hMembership⟩ := hChart p
    have hp₁ : p.val ∈ (chartAt (Space n) (x p)).source := by
      simpa only [extChartAt_source] using hpChart
    have hp₂ : (chartAt (Space n) (x p)) p.val ∈ (c p).source := by
      simpa [chartPt,ComplexModel] using hpSource
    have heZero : (e p) p.val = 0 := by
      simpa [e,chartPt,ComplexModel] using hpZero
    refine ⟨⟨hp₁,hp₂⟩,?_⟩
    change (e p) p.val ∈ Metric.ball 0 (1/8)
    rw [heZero]
    exact Metric.mem_ball_self (by norm_num)
  obtain ⟨s,hCover⟩ := hO.2.2.2.1.elim_finite_subcover U hUopen (by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p,hp⟩,hpU ⟨p,hp⟩⟩)
  let pick : Fin (Fintype.card s) → K := fun i => ((Fintype.equivFin s).symm i).val
  let A : AtlasData M :=
    { count := Fintype.card s
      center := fun i => x (pick i)
      forward := fun i => F05TotalForward (F05Sentinel n hn) (c (pick i))
      inverse := fun i => (c (pick i)).symm
      normal := fun i => ν (pick i) }
  have hSmallCover : closure O ⊆ ⋃ i, lift A i '' region (A.normal i) (1/8) := by
    intro y hy
    obtain ⟨j,hjs,hyU⟩ := mem_iUnion₂.mp (hCover hy)
    let i : Fin (Fintype.card s) := Fintype.equivFin s ⟨j,hjs⟩
    have hPick : pick i = j := by simp only [pick,i,Equiv.symm_apply_apply]
    let z : Space n := e j y
    have hzNorm : ‖z‖ < (1/8 : ℝ) := by
      change ‖e j y‖ < (1/8 : ℝ)
      have hh := hyU.2
      change e j y ∈ Metric.ball 0 (1/8) at hh
      simpa only [Metric.mem_ball,dist_zero_right] using hh
    have hyChart : y ∈ (chartAt (Space n) (x j)).source := hyU.1.1
    have hyCoord : (chartAt (Space n) (x j)) y ∈ (c j).source := hyU.1.2
    have hInv : (c j).symm z = chartPt (x j) y := by
      change (c j).symm ((c j) ((chartAt (Space n) (x j)) y)) = chartPt (x j) y
      rw [(c j).left_inv hyCoord]
      simp [chartPt,ComplexModel]
    have hLift : chartInv (x j) ((c j).symm z) = y := by
      rw [hInv]
      exact (extChartAt (ComplexModel n) (x j)).left_inv
        (by simpa only [extChartAt_source] using hyChart)
    have hzBall : z ∈ Metric.ball 0 3 := by
      rw [Metric.mem_ball,dist_zero_right]
      linarith
    obtain ⟨hOpen,hTarget,hF,hI,hImage,hRight,hLeft,hMembership⟩ :=
      F05_physical_chart_properties hn O j.val (x j) (ν j) (c j) (hChart j)
    have hClosed : match ν j with | none => True | some a => realCoord z a ≤ 0 := by
      have hh := ((hMembership z hzBall).2.1).mp (by rwa [hLift])
      cases hν : ν j <;> simpa only [hν,Option.elim] using hh
    apply mem_iUnion.mpr
    refine ⟨i,z,?_,?_⟩
    · change ‖z‖ ≤ (1/8 : ℝ) ∧ (match ν (pick i) with
        | none => True | some a => realCoord z a ≤ 0)
      rw [hPick]
      exact ⟨hzNorm.le,hClosed⟩
    · change chartInv (x (pick i)) ((c (pick i)).symm z) = y
      rw [hPick]
      exact hLift
  have hCoverOne : closure O ⊆ ⋃ i, lift A i '' region (A.normal i) 1 := by
    intro y hy
    obtain ⟨i,z,hz,rfl⟩ := mem_iUnion.mp (hSmallCover hy)
    exact mem_iUnion.mpr ⟨i,z,region_mono (A.normal i) (by norm_num : (1/8 : ℝ) ≤ 1) hz,rfl⟩
  refine ⟨A,?_,hSmallCover⟩
  refine ⟨?_,hCoverOne,?_⟩
  · intro i
    obtain ⟨hOpen,hTarget,hF,hI,hImage,hRight,hLeft,hMem⟩ :=
      F05_physical_chart_properties hn O (pick i).val (x (pick i)) (ν (pick i))
        (c (pick i)) (hChart (pick i))
    refine ⟨hOpen,hTarget,hF,hI,hImage,hRight,hLeft,?_⟩
    intro z hz
    have hh := hMem z hz
    cases hν : ν (pick i) <;> simpa only [A,lift,hν,Option.elim] using hh
  · intro k
    have hBounds (i : Fin A.count) : ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Metric.closedBall 0 2,
        ‖iteratedFDeriv ℝ k (A.inverse i) z‖ ≤ C ∧
        ‖iteratedFDeriv ℝ k (A.forward i) (A.inverse i z)‖ ≤ C :=
      F05_physical_chart_derivative_bounds hn O (pick i).val (x (pick i)) (ν (pick i))
        (c (pick i)) (hChart (pick i)) k
    choose C hC hBound using hBounds
    let B := 1 + ∑ i, C i
    have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i hi => (hC i).le)
    refine ⟨B,by dsimp only [B]; positivity,?_⟩
    intro i z hz
    have hSingle : C i ≤ ∑ j, C j := Finset.single_le_sum
      (fun j hj => (hC j).le) (Finset.mem_univ i)
    have hBudget : C i ≤ B := by dsimp only [B]; linarith
    exact ⟨((hBound i z hz).1).trans hBudget,((hBound i z hz).2).trans hBudget⟩

end Yau.Proofs.F05Aux

import Yau.LeafProofs.L16LocalCutoffBudgets
import Yau.LeafProofs.L16HolderOnlyClassicalEstimate

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- An actual compact localization of a bounded local classical solution
    acquires a uniform Schauder estimate from the constructed inverse. -/
theorem exists_uniform_localized_classical_schauder {n : ℕ} {α M lam upper : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M)
    {K : Set (Space n)} (hK : IsCompact K) :
    ∃ δ A : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < A ∧
      ∀ (h : ℝ) (hh : 0 < h), h ≤ 1 →
      ∀ (c : Space n) (O : Set (Space n)) (a : Point n → Mat n)
        (b : Point n → Yau.RIdx n → ℝ) (f u : Point n → ℝ) (F L B : ℝ),
      let T := localSchauderTime δ h
      let φ : Space n → ℝ := innerPatchBump (h/8) (by positivity) c
      IsOpen O → HolderBound α (cylinder Set.univ 0 T) a M →
      (∀ i, HolderBound α (cylinder Set.univ 0 T) (fun p => b p i) M) →
      Elliptic (cylinder Set.univ 0 T) a lam upper →
      (∀ p ∈ cylinder Set.univ 0 T, p.1 ∉ K → a p = 1) →
      tsupport φ ⊆ O →
      HolderBound α (cylinder O 0 T) (fun p => (u p,spatialD u p)) L →
      HolderBound α (cylinder O 0 T) f F →
      C2 (cylinder O 0 T) u → 0 ≤ B →
      (∀ p ∈ cylinder O 0 T, |u p| ≤ B) →
      (∀ p ∈ cylinder O 0 T, linearOp (cylinder O 0 T) a b u p = f p) →
      SchauderBound α (cylinder Set.univ 0 T)
        (fun p => initialTimeCutoff T p.2*(φ p.1*u p)) (A*(h⁻¹)^8*(F+L)) ∧
      HolderBound α (cylinder Set.univ 0 T)
        (fun p => (initialTimeCutoff T p.2*(φ p.1*u p),
          spatialD (fun q => initialTimeCutoff T q.2*(φ q.1*u q)) p))
        (A*(h⁻¹)^8*(F+L)) := by
  obtain ⟨δ,C,hδ,hδ1,hC,hEstimate⟩ :=
    exists_uniform_short_classical_schauder_estimate_holder_only
      (n := n) (M := M) (lam := lam) (upper := upper) hα hα1 hK
  obtain ⟨A0,hA0,hBudget⟩ :=
    exists_uniform_localized_classical_source_budget (n := n) hα hα1 hδ hδ1 hM
  refine ⟨δ,C*A0,hδ,hδ1,mul_pos hC hA0,?_⟩
  intro h hh hh1 c O a b f u F L B
  dsimp only
  let T : ℝ := localSchauderTime δ h
  let φ : Space n → ℝ := innerPatchBump (h/8) (by positivity) c
  intro hO ha hb hEll hExterior hSupport hLow hf hu hB0 hB hPDE
  let w : Point n → ℝ := fun p => initialTimeCutoff T p.2*(φ p.1*u p)
  let g : Point n → ℝ := fun p =>
    initialTimeCutoff T p.2*(φ p.1*f p-spatialCutoffCommutator a b φ u p)+
      deriv (initialTimeCutoff T) p.2*(φ p.1*u p)
  have hT : 0 < T := by dsimp only [T,localSchauderTime]; positivity
  have hTδ : T ≤ δ := by
    have hBoundH : h^2/8 ≤ 1 := by nlinarith
    calc
      T = δ*(h^2/8) := by dsimp only [T,localSchauderTime]; ring
      _ ≤ δ*1 := mul_le_mul_of_nonneg_left hBoundH hδ.le
      _ = δ := mul_one _
  have hφSmooth : ContDiff ℝ 2 φ := (innerPatchBump_contDiff (by positivity) c).of_le (by simp)
  have hθSmooth : ContDiff ℝ 1 (initialTimeCutoff T) :=
    (initialTimeCutoff_contDiff T).of_le (by simp)
  have hEquation := localized_classical_cutoff_equation hT hO hφSmooth hSupport hθSmooth hu a b hPDE
  have hSource : HolderBound α (cylinder Set.univ 0 T) g (A0*(h⁻¹)^8*(F+L)) :=
    hBudget h hh hh1 c O a b f u F L ha hb hSupport hLow hf
  have hBoundW (p : Point n) (hp : p ∈ cylinder Set.univ 0 T) : |w p| ≤ B := by
    by_cases hφ0 : φ p.1 = 0
    · dsimp only [w]
      rw [hφ0,zero_mul,mul_zero,abs_zero]
      exact hB0
    · have hpO : p.1 ∈ O := hSupport (subset_closure hφ0)
      have hφNonneg : 0 ≤ φ p.1 := (innerPatchBump (h/8) (by positivity) c).nonneg
      have hφOne : φ p.1 ≤ 1 := (innerPatchBump (h/8) (by positivity) c).le_one
      have hθBounds := initialTimeCutoff_mem_Icc T p.2
      have hProduct : initialTimeCutoff T p.2*φ p.1 ≤ 1 :=
        (mul_le_mul hθBounds.2 hφOne hφNonneg (by norm_num)).trans_eq (one_mul _)
      dsimp only [w]
      rw [abs_mul,abs_mul,abs_of_nonneg hθBounds.1,abs_of_nonneg hφNonneg]
      calc
        _ = (initialTimeCutoff T p.2*φ p.1)*|u p| := by ring
        _ ≤ 1*B := mul_le_mul hProduct (hB p ⟨hpO,hp.2⟩) (abs_nonneg _) (by norm_num)
        _ = B := one_mul _
  have hInit (x : Space n) : w (x,0) = 0 := by
    dsimp only [w]
    rw [initialTimeCutoff_initial,zero_mul]
  have hResult := hEstimate T a b g w (A0*(h⁻¹)^8*(F+L)) B hT hTδ ha hb hEll hExterior
    hSource hEquation.1 hBoundW hInit hEquation.2
  have hScale : C*(A0*(h⁻¹)^8*(F+L)) = (C*A0)*(h⁻¹)^8*(F+L) := by ring
  rw [hScale] at hResult
  exact hResult

end Yau.LeafProofs.L16Aux

import Yau.LeafProofs.L16WordBootstrap
import Yau.LeafProofs.L16JointBootstrap

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem classical_solution_contDiffOn_infty {n : ℕ} {α T U lam upper : ℝ}
    (hT : 0 < T) (hα : 0 < α) (hα1 : α < 1)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {f u : Point n → ℝ}
    (hSmooth : SmoothCoefficients (cylinder Set.univ 0 T) a b)
    (hfSmooth : ContDiffOn ℝ ∞ f (cylinder Set.univ 0 T))
    (hEll : Elliptic (cylinder Set.univ 0 T) a lam upper)
    {K : Set (Space n)} (hK : IsCompact K)
    (hExterior : ∀ x ∉ K, ∀ t ∈ Set.Icc 0 T,
      a (x,t) = 1 ∧ b (x,t) = 0 ∧ f (x,t) = 0)
    (hu : SchauderBound α (cylinder Set.univ 0 T) u U)
    (huLow : HolderBound α (cylinder Set.univ 0 T) (fun p => (u p,spatialD u p)) U)
    (hInit : ∀ x, u (x,0) = 0)
    (hOp : ∀ p ∈ cylinder Set.univ 0 T, linearOp (cylinder Set.univ 0 T) a b u p = f p) :
    ContDiffOn ℝ ∞ u (cylinder Set.univ 0 T) := by
  have hI := smooth_compact_wordInvariant_all hT hα hα1 hSmooth hfSmooth hEll hK hExterior hu huLow hInit hOp
  have hC2 (w : List (Space n)) : C2 (cylinder Set.univ 0 T) (spatialWordDerivative w u) := by
    obtain ⟨C,hC,_,_,_⟩ := hI w.length w le_rfl
    exact hC.1
  have hPDE (w : List (Space n)) (p : Point n) (hp : p ∈ cylinder Set.univ 0 T) :
      linearOp (cylinder Set.univ 0 T) a b (spatialWordDerivative w u) p = wordSource a b f u w p := by
    obtain ⟨C,_,_,_,hC⟩ := hI w.length w le_rfl
    exact hC p hp
  exact contDiffOn_infty_of_spatialWords_c2_pde hT hC2 hPDE
    (fun s => (smooth_cylinder_spatialWordDerivative hT hK hSmooth.1
      (fun x hx t ht => (hExterior x hx t ht).1) s).1)
    (fun s i => (smooth_cylinder_spatialWordDerivative hT hK (hSmooth.2 i) (c := (0 : ℝ))
      (fun x hx t ht => by rw [(hExterior x hx t ht).2.1]; rfl) s).1)
    (fun s => (smooth_cylinder_spatialWordDerivative hT hK hfSmooth
      (fun x hx t ht => (hExterior x hx t ht).2.2) s).1)

/-- The exact global zero-initial Cauchy consumer, with genuine smoothness
on the closed slab and no extra extension or corner compatibility assumptions. -/
theorem zeroInitialCauchySolution : ZeroInitialCauchySolution := by
  unfold ZeroInitialCauchySolution
  intro n _hn T lam upper hT a b f
  dsimp only
  intro hSmooth hfSmooth hEll hExterior
  obtain ⟨K,hK,hOutside⟩ := hExterior
  obtain ⟨u,D,hu,hLow,h0,hOp⟩ := smooth_compact_global_classical_solution
    (α := (1/2 : ℝ)) hT (by norm_num) (by norm_num) hSmooth hfSmooth hEll hK hOutside
  refine ⟨u,classical_solution_contDiffOn_infty hT (by norm_num) (by norm_num)
    hSmooth hfSmooth hEll hK hOutside hu hLow h0 hOp,h0,⟨D,?_⟩,hOp⟩
  intro p hp
  exact (hu.2.2.1 p hp).1

end Yau.LeafProofs.L16Aux

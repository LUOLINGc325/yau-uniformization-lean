import Yau.Proofs.F05ExponentialOpenEquation
import Yau.Proofs.F05PhysicalManifoldOperator
import Yau.Proofs.F05HolderGauge

/-! Once genuine positive-time regularity is proved, the original manifold
PDE supplies the exact exponential equation on the entire open radius-three
physical patch. The artificial radius-two receiving rim is not an equation boundary. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.ParabolicCandidates Yau.F05Transport Yau.LeafProofs.L16Aux
open Yau.LeafProofs.L16ExpBoundaryAux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_timeD_open_pull (A : AtlasData M) (i : Fin A.count) (T : ℝ)
    (w : M.Carrier → ℝ → ℝ) {p : Point n}
    (hp : p ∈ (F05ModelOpen A i ∩ Metric.ball 0 3) ×ˢ Ioc 0 T) :
    timeD ((F05ModelOpen A i ∩ Metric.ball 0 3) ×ˢ Ioc 0 T) (pull A i w) p =
      derivWithin (w (lift A i p.1)) (Icc 0 T) p.2 := by
  rw [← timeD_closed_eq_halfOpen hp (pull A i w)]
  have hFiber : {t | (p.1,t) ∈ cylinder (closure (F05ModelOpen A i ∩ Metric.ball 0 3)) 0 T} =
      Icc 0 T := by
    ext t
    simp only [cylinder,mem_prod,mem_ofPred_eq,subset_closure hp.1,true_and]
  simp only [timeD,hFiber,pull]

theorem F05_physical_exp_equation_open {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (R w : M.Carrier → ℝ → ℝ)
    {T : ℝ} (hT : 0 < T) (hh : MetricFamilySmooth h (Icc 0 T))
    (hSmooth : ∀ i, ContDiffOn ℝ ∞ (pull A i w)
      ((F05ModelOpen A i ∩ Metric.ball 0 3) ×ˢ Ioc 0 T))
    (hEquation : ∀ x ∈ closure O, ∀ t ∈ Icc 0 T,
      derivWithin (w x) (Icc 0 T) t = Real.exp (-w x t)*laplacian (h t) (fun y => w y t) x+
        (1-Real.exp (-w x t))*R x t) (i : Fin A.count) :
    ExpDivergenceEquation ((F05ModelOpen A i ∩ Metric.ball 0 3) ×ˢ Ioc 0 T)
      (fun p => flatA (h p.2) A i p) (fun p j => flatB (h p.2) A i p j)
      (pull A i R) (pull A i (fun x t => Real.exp (w x t))) := by
  have hOpen : IsOpen (F05ModelOpen A i ∩ Metric.ball 0 3) := by
    rw [F05ModelOpen_eq]
    exact (F05FlatOpen_isOpen _).inter Metric.isOpen_ball
  apply F05_exp_divergence_equation_open hOpen hT
    ((F05_flat_coefficients_smooth hA h hh i).1.mono
      (fun p hp => ⟨hp.1.2,hp.2.1.le,hp.2.2⟩)) (hSmooth i)
  intro p hp
  have hSlice : ContDiffOn ℝ ∞ (fun z => pull A i w (z,p.2))
      (F05ModelOpen A i ∩ Metric.ball 0 3) :=
    (hSmooth i).comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun z hz => ⟨hz,hp.2⟩)
  have hSpatial := (hSlice.contDiffAt (hOpen.mem_nhds hp.1)).of_le (by simp : (2 : ℕ∞ω) ≤ ∞)
  have hPhysical := ((hA.1 i).2.2.2.2.2.2.2 p.1 hp.1.2).1
  have hxO : lift A i p.1 ∈ O := by
    apply hPhysical.mpr
    have hx := hp.1.1
    cases hn : A.normal i <;> simpa only [F05ModelOpen,hn,mem_ofPred_eq] using hx
  have hEq := hEquation (lift A i p.1) (subset_closure hxO) p.2 ⟨hp.2.1.le,hp.2.2⟩
  have hLap := F05_flattened_laplacian_C2 hA (h p.2) i (fun x => w x p.2) hp.1.2 hSpatial
  change laplacian (h p.2) (fun x => w x p.2) (lift A i p.1) =
    (∑ j,∑ k,flatA (h p.2) A i p j k*spatialDD (pull A i w) p (realVec j) (realVec k))+
      ∑ j,flatB (h p.2) A i p j*spatialD (pull A i w) p (realVec j) at hLap
  unfold linearOp
  rw [F05_timeD_open_pull A i T w hp]
  simp only [Matrix.smul_apply,smul_eq_mul,mul_assoc,← Finset.mul_sum]
  dsimp only [pull] at hEq ⊢
  linear_combination hEq+Real.exp (-w (lift A i p.1) p.2)*hLap

end Yau.Proofs.F05Aux

import Yau.Proofs.D05AmbientBivector
import Yau.Proofs.D05EmbeddedDiscTrivialization

/-! The actual image bundle of dG along the supplied disc meets the
local-projection, rank and exact-generator hypotheses of rank induction. -/

open scoped Manifold Topology ContDiff Matrix
noncomputable section
namespace Yau.Blueprint.D05Proof
open Yau V03Proof BundlePresentation

theorem toEuclideanLin_reindex_domain_apply {ι κ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype τ] [DecidableEq τ]
    (A : Matrix κ ι ℂ) (e : ι ≃ τ) (v : EuclideanSpace ℂ τ) :
    Matrix.toEuclideanLin (A.submatrix id e.symm) v =
      Matrix.toEuclideanLin A (WithLp.toLp 2 (fun i => v (e i))) := by
  apply WithLp.ofLp_injective
  exact Matrix.submatrix_mulVec_equiv A (WithLp.ofLp v) id e.symm

theorem range_matrix_reindex_domain {ι κ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype τ] [DecidableEq τ]
    (A : Matrix κ ι ℂ) (e : ι ≃ τ) :
    LinearMap.range (Matrix.toEuclideanLin (A.submatrix id e.symm)) =
      LinearMap.range (Matrix.toEuclideanLin A) := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact ⟨WithLp.toLp 2 (fun i => v (e i)), (toEuclideanLin_reindex_domain_apply A e v).symm⟩
  · rintro _ ⟨v, rfl⟩
    refine ⟨WithLp.toLp 2 (fun j => v (e.symm j)), ?_⟩
    rw [toEuclideanLin_reindex_domain_apply]
    simp

theorem toEuclideanLin_injective_of_mulVec {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix κ ι ℂ) (hA : Function.Injective A.mulVec) :
    Function.Injective (Matrix.toEuclideanLin A) := by
  intro u v huv
  apply WithLp.ofLp_injective
  apply hA
  exact congrArg WithLp.ofLp huv

theorem toEuclideanLin_reindex_domain_injective {ι κ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype τ] [DecidableEq τ]
    (A : Matrix κ ι ℂ) (e : ι ≃ τ) (hA : Function.Injective A.mulVec) :
    Function.Injective (Matrix.toEuclideanLin (A.submatrix id e.symm)) := by
  intro u v huv
  rw [toEuclideanLin_reindex_domain_apply, toEuclideanLin_reindex_domain_apply] at huv
  have h := toEuclideanLin_injective_of_mulVec A hA huv
  ext j
  simpa using congrArg (fun w : EuclideanSpace ℂ ι => w (e.symm j)) h

variable {n q : ℕ} {M : ComplexManifold n}

def cotangentIndexFin : CotangentIndex n ≃ Fin (Fintype.card (CotangentIndex n)) :=
  Fintype.equivFin _

def dgFin (G : CotangentPoint M → ComplexVector q) (x : M.Carrier) (y : CotangentPoint M) :
    Matrix (Fin q) (Fin (Fintype.card (CotangentIndex n))) ℂ :=
  (cotangentDG G x y).submatrix id cotangentIndexFin.symm

def cotangentImageBundle (G : CotangentPoint M → ComplexVector q)
    (f : ℂ → CotangentPoint M) (z : ℂ) : Submodule ℂ (ComplexVector q) :=
  LinearMap.range (Matrix.toEuclideanLin (cotangentDG G (f z).1 (f z)))

theorem cotangentDG_range_in_fixed_chart {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentHolomorphic G) (x : M.Carrier) (y : CotangentPoint M)
    (hy : y ∈ cotangentSource x) :
    LinearMap.range (Matrix.toEuclideanLin (cotangentDG G x y)) =
      LinearMap.range (Matrix.toEuclideanLin (cotangentDG G y.1 y)) := by
  apply le_antisymm
  · rw [cotangentDG_transition hG x y.1 y hy (mem_extChartAt_source _)]
    exact matrix_range_mul_le _ _
  · rw [cotangentDG_transition hG y.1 x y (mem_extChartAt_source _) hy]
    exact matrix_range_mul_le _ _

theorem original_ambient_bundle_generated {G : CotangentPoint M → ComplexVector q}
    {f : ℂ → CotangentPoint M} {R : ℝ} (hG : CotangentImmersion G)
    (hf : CotangentHolomorphicOn f (Metric.closedBall (0 : ℂ) R)) :
    LocallyProjectedOn (cotangentImageBundle G f) (Metric.ball 0 R) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) R,
      Module.finrank ℂ (cotangentImageBundle G f z) = Fintype.card (CotangentIndex n)) ∧
    (∀ a : Fin q, ContDiffOn ℂ ∞ (fun z => ambientBivectorColumn G a (f z))
      (Metric.ball 0 R)) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) R,
      Submodule.span ℂ (Set.range fun a => ambientBivectorColumn G a (f z)) =
        cotangentImageBundle G f z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply locallyProjectedOn_of_local_frames (r := Fintype.card (CotangentIndex n))
    intro p hp
    obtain ⟨V, hV, hpV, hsource, hcoord⟩ := hf.2 p (Metric.ball_subset_closedBall hp)
    let O := Metric.ball (0 : ℂ) R ∩ V
    have hOS : O ⊆ Metric.closedBall (0 : ℂ) R ∩ V :=
      fun z hz => ⟨Metric.ball_subset_closedBall hz.1, hz.2⟩
    refine ⟨O, Metric.isOpen_ball.inter hV, ⟨hp, hpV⟩, Set.inter_subset_left,
      fun z => dgFin G (f p).1 (f z), ?_, ?_, ?_⟩
    · intro a j z hz
      exact (cotangentDG_entry_contDiffWithinAt hG.1 (f p).1
        (hsource z (hOS hz)) (hcoord z (hOS hz)) a (cotangentIndexFin.symm j)).mono hOS
    · exact toEuclideanLin_reindex_domain_injective _ cotangentIndexFin
        (cotangentDG_mulVec_injective_in_chart hG (f p).1 (f p) (mem_extChartAt_source _))
    · intro z hz
      exact (range_matrix_reindex_domain _ cotangentIndexFin).trans
        (cotangentDG_range_in_fixed_chart hG.1 (f p).1 (f z) (hsource z (hOS hz)))
  · intro z _
    exact (LinearMap.finrank_range_of_inj
      (toEuclideanLin_injective_of_mulVec _ (cotangentDG_mulVec_injective hG (f z)))).trans
      finrank_euclideanSpace
  · intro a
    exact (cotangentHolomorphicOn_ambient_contDiffOn hf
      (ambientBivectorColumn_holomorphic hG.1 a)).mono Metric.ball_subset_closedBall
  · intro z _
    exact ambientBivector_columns_span hG (f z)

end Yau.Blueprint.D05Proof

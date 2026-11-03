import Yau.Proofs.D05InitialAmbientFrame
import Yau.Proofs.D05NormalizeColumns

/-! The original extended disc admits a normalized frame for the same G.
The finite-index transport preserves the Euclidean Gram identity exactly. -/

open scoped Topology ContDiff Matrix
noncomputable section
namespace Yau.Blueprint.D05Proof
open Yau V03Proof

theorem matrix_column_gram_reindex {ι κ τ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Fintype τ] [DecidableEq τ]
    (A : Matrix κ τ ℂ) (e : ι ≃ τ) (hA : Matrix.conjTranspose A * A = 1) :
    Matrix.conjTranspose (A.submatrix id e) * (A.submatrix id e) = 1 := by
  ext i j
  have h := congrFun (congrFun hA (e i)) (e j)
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply,
    id_eq, Matrix.one_apply, Equiv.apply_eq_iff_eq] using h

theorem original_normalized_frame_exists {n q : ℕ} {M : ComplexManifold n}
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {f : ℂ → CotangentPoint M} (hf : ExtendedCotangentDisc f) :
    ∃ E : ℂ → CotangentMatrix n, NormalizedDiscFrame G f E := by
  classical
  obtain ⟨ρ, V, hρ, hV, hiV⟩ := original_initial_ambient_frame hG hf
  obtain ⟨W, hW, hiW, hbW⟩ := normalize_ambient_columns hρ V hV (fun z hz => (hiV z hz).1)
  let W' : ℂ → Matrix (Fin q) (CotangentIndex n) ℂ :=
    fun z => (W z).submatrix id cotangentIndexFin
  have hD : Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball 0 ρ :=
    Metric.closedBall_subset_ball hρ
  have hiW' : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, Function.Injective (W' z).mulVec := by
    intro z hz u v huv
    change (W z).submatrix id cotangentIndexFin *ᵥ u =
      (W z).submatrix id cotangentIndexFin *ᵥ v at huv
    rw [Matrix.submatrix_mulVec_equiv, Matrix.submatrix_mulVec_equiv] at huv
    have h := (hiW z hz).1 huv
    funext i
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
      congrFun h (cotangentIndexFin i)
  have hrW' : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      LinearMap.range (Matrix.toEuclideanLin (W' z)) = cotangentImageBundle G f z := by
    intro z hz
    exact (range_matrix_reindex_domain (W z) cotangentIndexFin.symm).trans
      ((hiW z hz).2.trans (hiV z (hD hz)).2)
  have hcolW' : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∀ j,
      ∃ u : CotangentIndex n → ℂ,
        cotangentDG G (f z).1 (f z) *ᵥ u = fun a => W' z a j := by
    intro z hz j
    have hc : (WithLp.toLp 2 (fun a => W' z a j) : ComplexVector q) ∈
        LinearMap.range (Matrix.toEuclideanLin (W' z)) := by
      refine ⟨EuclideanSpace.single j 1, ?_⟩
      ext a
      simp [Matrix.toLpLin_apply, EuclideanSpace.single]
    rw [hrW' z hz] at hc
    obtain ⟨u, hu⟩ := hc
    exact ⟨WithLp.ofLp u, congrArg WithLp.ofLp hu⟩
  obtain ⟨hE, hEV⟩ := ambient_frame_lift_is_frame hG
    (extendedCotangentDisc_cotangentDisc hf) W'
    (fun a j => hW a (cotangentIndexFin j)) hiW' hcolW'
  refine ⟨centeredAmbientLift G f W', normalizedFrame_of_boundary hG hE ?_⟩
  intro θ
  rw [hEV _ (circlePoint_mem_closedBall θ)]
  exact matrix_column_gram_reindex (W (circlePoint θ)) cotangentIndexFin (hbW θ)

end Yau.Blueprint.D05Proof

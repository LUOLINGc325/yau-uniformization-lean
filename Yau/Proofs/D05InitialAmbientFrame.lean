import Yau.Proofs.D05GeneratedBundle
import Yau.Proofs.D05DiscRestriction

/-! Rank induction applied to the original immersion and the same original
extended disc, producing an actual ambient frame on a larger open disc. -/

open scoped Topology ContDiff Matrix
noncomputable section
namespace Yau.Blueprint.D05Proof
open Yau V03Proof

theorem matrix_mulVec_injective_of_independent_columns {ι κ : Type*}
    [Fintype ι] [Fintype κ] (A : Matrix κ ι ℂ)
    (hA : LinearIndependent ℂ (fun j =>
      (WithLp.toLp 2 (fun i => A i j) : EuclideanSpace ℂ κ))) :
    Function.Injective A.mulVec := by
  intro u v huv
  apply hA.fintypeLinearCombination_injective
  apply WithLp.ofLp_injective
  funext i
  simp only [Fintype.linearCombination_apply, WithLp.ofLp_sum, WithLp.ofLp_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have h := congrFun huv i
  simpa only [Matrix.mulVec, dotProduct, mul_comm] using h

theorem original_initial_ambient_frame {n q : ℕ} {M : ComplexManifold n}
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {f : ℂ → CotangentPoint M} (hf : ExtendedCotangentDisc f) :
    ∃ (ρ : ℝ) (V : ℂ → Matrix (Fin q) (Fin (Fintype.card (CotangentIndex n))) ℂ),
      1 < ρ ∧
      (∀ a j, ContDiffOn ℂ ∞ (fun z => V z a j) (Metric.ball 0 ρ)) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) ρ, Function.Injective (V z).mulVec ∧
        LinearMap.range (Matrix.toEuclideanLin (V z)) = cotangentImageBundle G f z := by
  classical
  obtain ⟨R, hR, hfR⟩ := extendedCotangentDisc_holomorphicOn hf
  obtain ⟨hB, hr, hs, hspan⟩ := original_ambient_bundle_generated hG hfR
  let ρ := (1 + R) / 2
  have hρ : 1 < ρ := by dsimp [ρ]; linarith
  have hρR : ρ < R := by dsimp [ρ]; linarith
  obtain ⟨v, hv, hvB⟩ := embedded_frame_on_smaller_disc
    (Fintype.card (CotangentIndex n)) q q ρ R (cotangentImageBundle G f)
    (fun a z => ambientBivectorColumn G a (f z)) (lt_trans zero_lt_one hρ) hρR
    hB hr hs hspan
  let V : ℂ → Matrix (Fin q) (Fin (Fintype.card (CotangentIndex n))) ℂ :=
    fun z a j => v j z a
  refine ⟨ρ, V, hρ, ?_, ?_⟩
  · intro a j
    exact (contDiffOn_piLp 2).mp (hv j) a
  · intro z hz
    have hc : (fun j => (WithLp.toLp 2 (fun a => V z a j) : ComplexVector q)) =
        fun j => v j z := by rfl
    refine ⟨matrix_mulVec_injective_of_independent_columns _ (hc.symm ▸ (hvB z hz).1), ?_⟩
    rw [← span_matrix_columns_eq_range, hc]
    exact (hvB z hz).2

end Yau.Blueprint.D05Proof

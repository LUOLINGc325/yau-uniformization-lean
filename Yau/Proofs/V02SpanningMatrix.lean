import Yau.Proofs.V02Minors
import Yau.Proofs.V03FrameSmooth

/-! The actual global spanning fields and immersion give a strictly positive
sum of all maximal minors, including dimension zero. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

theorem vecMul_injective_of_span_columns {ι β : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (T : Matrix ι β ℂ) (hT : Submodule.span ℂ (Set.range T.col) = ⊤) :
    Function.Injective T.vecMul := by
  have hsurj : Function.Surjective T.mulVecLin :=
    LinearMap.range_eq_top.mp ((Matrix.range_mulVecLin T).trans hT)
  intro u v huv
  ext i
  obtain ⟨w, hw⟩ := hsurj (Pi.single i 1)
  change T *ᵥ w = Pi.single i 1 at hw
  have hh := congrArg (fun z : β → ℂ => z ⬝ᵥ w) huv
  simpa only [← Matrix.dotProduct_mulVec, hw, dotProduct_single_one] using hh

theorem field_gram_posDef {ι β : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (T : Matrix ι β ℂ) (hT : Submodule.span ℂ (Set.range T.col) = ⊤) :
    (T * Tᴴ).PosDef :=
  Matrix.PosDef.mul_conjTranspose_self T (vecMul_injective_of_span_columns T hT)

variable {n q b : ℕ} {M : ComplexManifold n}

def fieldMatrix (Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ)
    (y : CotangentPoint M) : Matrix (CotangentIndex n) (Fin b) ℂ :=
  fun i k => Z k y i

def spanningAmbientMatrix (G : CotangentPoint M → ComplexVector q)
    (Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ)
    (y : CotangentPoint M) : Matrix (Fin q) (Fin b) ℂ :=
  cotangentDG G y.1 y * fieldMatrix Z y

def spanningMinorSq (G : CotangentPoint M → ComplexVector q)
    (Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ)
    (y : CotangentPoint M) : ℝ :=
  tupleMinorSq (cotangentDG G y.1 y) (fieldMatrix Z y)

theorem spanningMinorSq_pos {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G)
    {Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ}
    (hZ : ∀ y, Submodule.span ℂ (Set.range (fun k => Z k y)) = ⊤)
    (y : CotangentPoint M) : 0 < spanningMinorSq G Z y := by
  apply tupleMinorSq_pos
  · exact V03Proof.cotangentDG_gram_posDef hG y
  · exact field_gram_posDef _ (hZ y)

end Yau.Blueprint.V02Proof

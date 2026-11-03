import Yau.Proofs.G04Whitening
import Yau.Blueprint.Nodes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

open Matrix
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- Positive definiteness supplies a genuine uniform scalar lower bound.
The empty matrix algebra is handled before using a nonempty spectrum. -/
theorem posDef_exists_scalar_lower {n : ℕ} (A : Herm n) (hA : A.PosDef) :
    ∃ c : ℝ, 0 < c ∧ (A-(c:ℂ) • (1:Herm n)).PosSemidef := by
  classical
  by_cases hs : Subsingleton (Herm n)
  · haveI := hs
    refine ⟨1,by norm_num,?_⟩
    have hz : A-((1:ℝ):ℂ) • (1:Herm n) = 0 := Subsingleton.elim _ _
    rw [hz]
    exact Matrix.PosSemidef.zero
  · haveI : Nontrivial (Herm n) := not_subsingleton_iff_nontrivial.mp hs
    obtain ⟨c,hc,hLower⟩ :=
      (CFC.exists_pos_algebraMap_le_iff A hA.isHermitian.isSelfAdjoint).mpr
        (fun r hr => hA.isStrictlyPositive.spectrum_pos hr)
    have hAlg : algebraMap ℝ (Herm n) c = (c:ℂ) • (1:Herm n) := by
      ext i j
      simp [Algebra.algebraMap_eq_smul_one,Matrix.smul_apply,Complex.real_smul]
    have hPSD := Matrix.le_iff.mp hLower
    exact ⟨c,hc,by simpa only [hAlg] using hPSD⟩

end Yau.NodeProofs.E02Aux

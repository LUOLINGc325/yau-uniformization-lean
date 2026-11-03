import Yau.LeafProofs.L17HermitianMatrixAssembly
import Yau.Proofs.F01LaplacianLinearity

/-! Actual positive native potential matrices construct a genuine
Hermitian flow using the canonical differential frame. Outside the stated
time domain the field is the original metric. -/
noncomputable section
open Set
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17HermitianMatrixAssemblyAux
variable {n : ℕ} {M : ComplexManifold n}

def nativePotentialMatrix (g : HermitianField M) (U : M.Carrier → ℝ → ℝ)
    (t : ℝ) (x : M.Carrier) : Matrix (Fin n) (Fin n) ℂ :=
  gMat g x - (t : ℂ) • ricci g x + levi (fun y => U y t) x

def assembledPotentialFlow (g : HermitianField M) (U : M.Carrier → ℝ → ℝ)
    (I : Set ℝ) (hpos : ∀ t ∈ I, ∀ x, (nativePotentialMatrix g U t x).PosDef) :
    ℝ → HermitianField M := by
  classical
  exact fun t => if ht : t ∈ I then
    hermitianFieldOfMatrices (nativePotentialMatrix g U t) (hpos t ht) else g

theorem assembledPotentialFlow_native_matrix
    (g : HermitianField M) (U : M.Carrier → ℝ → ℝ) (I : Set ℝ)
    (hpos : ∀ t ∈ I, ∀ x, (nativePotentialMatrix g U t x).PosDef)
    {t : ℝ} (ht : t ∈ I) (x : M.Carrier) :
    gMat (assembledPotentialFlow g U I hpos t) x =
      gMat g x - (t : ℂ) • ricci g x + levi (fun y => U y t) x := by
  classical
  simp only [assembledPotentialFlow, dif_pos ht]
  exact gMat_hermitianFieldOfMatrices _ _ x

theorem assembledPotentialFlow_initial
    (g : HermitianField M) (U : M.Carrier → ℝ → ℝ) (I : Set ℝ)
    (hpos : ∀ t ∈ I, ∀ x, (nativePotentialMatrix g U t x).PosDef)
    (hzero : 0 ∈ I) (hU0 : ∀ x, U x 0 = 0) :
    assembledPotentialFlow g U I hpos 0 = g := by
  apply hermitianField_ext
  intro x
  rw [assembledPotentialFlow_native_matrix g U I hpos hzero x]
  have he : (fun y => U y 0) = (fun _ => (0 : ℝ)) := funext hU0
  rw [he, levi_const_native]
  simp

end Yau.NodeProofs.F01Aux

import Yau.Proofs.F01MatrixLimitOrder
import Yau.LeafProofs.L17HermitianMatrixAssembly
import Yau.LeafProofs.L17ChartNaturality

/-! Pointwise native matrix limits and an actual uniform positive
lower order construct a Hermitian field. Its canonical matrices and
every actual chart pullback are the limits of the original fields. -/
noncomputable section
open Set Filter
open scoped Topology Manifold Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HermitianMatrixAssemblyAux
variable {n : ℕ} {M : ComplexManifold n}

theorem hermitian_field_of_native_matrix_limits
    (g : HermitianField M) (k : ℕ → HermitianField M)
    {ell C : ℝ} (hell : 0 < ell)
    (hExists : ∀ x : M.Carrier, ∃ H : Matrix (Fin n) (Fin n) ℂ,
      Tendsto (fun m => gMat (k m) x) atTop (𝓝 H))
    (hLower : ∀ m x, (gMat (k m) x - (ell : ℂ) • gMat g x).PosSemidef)
    (hUpper : ∀ m x, ((C : ℂ) • gMat g x - gMat (k m) x).PosSemidef) :
    ∃ K : HermitianField M,
      (∀ x, Tendsto (fun m => gMat (k m) x) atTop (𝓝 (gMat K x))) ∧
      (∀ x, (gMat K x - (ell : ℂ) • gMat g x).PosSemidef ∧
        ((C : ℂ) • gMat g x - gMat K x).PosSemidef) ∧
      ∀ (e : ComplexVector n → M.Carrier) (z : ComplexVector n),
        Tendsto (fun m => pullbackMatrix (k m) e z) atTop (𝓝 (pullbackMatrix K e z)) := by
  classical
  choose H hH using hExists
  have hEntry (x : M.Carrier) (i j : Fin n) :
      Tendsto (fun m => gMat (k m) x i j) atTop (𝓝 (H x i j)) := by
    have hEval : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ => A i j) :=
      (continuous_apply j).comp (continuous_apply i)
    exact hEval.continuousAt.tendsto.comp (hH x)
  have hOrders (x : M.Carrier) :
      (H x - (ell : ℂ) • gMat g x).PosSemidef ∧
        ((C : ℂ) • gMat g x - H x).PosSemidef := by
    constructor
    · exact matrix_lower_order_of_entry_limits (fun _ => gMat g x)
        (fun m => gMat (k m) x) (gMat g x) (H x) ell
        (fun _ _ => tendsto_const_nhds) (hEntry x) (Eventually.of_forall (fun m => hLower m x))
    · exact matrix_upper_order_of_entry_limits (fun _ => gMat g x)
        (fun m => gMat (k m) x) (fun _ => C) (gMat g x) (H x) C
        (fun _ _ => tendsto_const_nhds) (hEntry x) tendsto_const_nhds
        (Eventually.of_forall (fun m => hUpper m x))
  have hPos (x : M.Carrier) : (H x).PosDef :=
    matrix_posDef_of_positive_lower_order (canonical_gMat_posDef g x) hell (hOrders x).1
  let K : HermitianField M := hermitianFieldOfMatrices H hPos
  have hKM (x : M.Carrier) : gMat K x = H x := gMat_hermitianFieldOfMatrices H hPos x
  refine ⟨K, (fun x => by simpa only [hKM x] using hH x),
    (fun x => by simpa only [hKM x] using hOrders x), ?_⟩
  intro e z
  let J := linearMatrix (coordinateDifferential e (e z) z)
  have hCong (v : HermitianField M) : pullbackMatrix v e z = Jᴴ * gMat v (e z) * J :=
    pullbackMatrix_eq_congruence v e (e z) z (mem_extChartAt_source (e z))
  have hNative : Tendsto (fun m => gMat (k m) (e z)) atTop (𝓝 (gMat K (e z))) := by
    simpa only [hKM] using hH (e z)
  have hh : Tendsto (fun m => Jᴴ * gMat (k m) (e z) * J) atTop
      (𝓝 (Jᴴ * gMat K (e z) * J)) :=
    (tendsto_const_nhds.mul hNative).mul tendsto_const_nhds
  simpa only [← hCong] using hh

end Yau.NodeProofs.F01Aux

import Yau.Proofs.F05NonlinearInitial
import Yau.Proofs.F05NonlinearHolder
import Yau.Proofs.F05JetLaplacian
import Yau.Proofs.F05LaplacianAdd

/-! The scalar Holder expression is exactly the original nonlinear source
in each full physical chart, including the original closed boundary. -/

open Set
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_nonlinear_correction_eq_chart {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (h : ℝ → HermitianField M) (p : M.Carrier → ℝ → ℝ) (α : ℝ)
    {T : ℝ} (hT : 0 < T) (hP : ∀ i, C2 (F05Q A i T) (pull A i p))
    (u : F05CompatibleJetGraph A α hT.le) (i : Fin A.count) {q : Point n} (hq : q ∈ F05Q A i T) :
    pull A i (F05NonlinearCorrection h T p (F05CanonicalJetFunction A χ α hT.le u)) q =
      F05ScalarCorrection (pull A i (fun x t => Real.exp (-p x t)))
        (pull A i (fun x t => laplacian (h t) (fun y => p y t) x))
        (pull A i (fun x t => scalarCurvature (h t) x))
        (pull A i (F05IntrinsicLinearOperator (fun x t => Real.exp (-p x t)) h T p))
        (F05CanonicalPull A χ α hT.le u i) (F05JetLaplacian A h α hT.le u i) q := by
  have hZ (j : Fin A.count) := (F05CanonicalJetFunction_realizes hA hχ α hT u j).1
  have hAdd := F05_laplacian_add_C2 hA h T p (F05CanonicalJetFunction A χ α hT.le u)
    hP hZ (F05D_lift_mem_closure hA hq.1) hq.2
  have hLap := F05JetLaplacian_eq_intrinsic hA hχ h α hT u i hq
  have hExp : Real.exp (-p (lift A i q.1) q.2)*
      Real.exp (-F05CanonicalJetFunction A χ α hT.le u (lift A i q.1) q.2) =
        Real.exp (-(p (lift A i q.1) q.2+F05CanonicalJetFunction A χ α hT.le u (lift A i q.1) q.2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold pull F05NonlinearCorrection F05ScalarCorrection F05CanonicalPull
  rw [hAdd,hLap]
  rw [mul_sub,mul_one,hExp]

end Yau.Proofs.F05Aux

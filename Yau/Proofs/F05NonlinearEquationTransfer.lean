import Yau.Proofs.F05PhysicalSlabJets
import Yau.Proofs.F05ClosedChartEquation
import Yau.Proofs.F05CofinalNonlinearLimit

/-! Physical value reconstruction transfers the original nonlinear PDE
to the fixed-cylinder field. Its actual derivatives then give exactly the
encoded equation used by the cofinal nonlinear limit. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_physical_nonlinear_equation_transfer {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) {a b T S : ℝ}
    (hab : a < b) (ha : 0 ≤ a) (hbT : b ≤ T) (hbS : b ≤ S)
    (u v : M.Carrier → ℝ → ℝ) (hu : ∀ i, C2 (F05Q A i T) (pull A i u))
    (hv : ∀ i, C2 (F05Q A i S) (pull A i v))
    (hEq : ∀ x ∈ closure O, ∀ t ∈ Icc a b, u x t = v x t)
    (hVEq : ∀ x ∈ closure O, ∀ t ∈ Icc 0 S,
      derivWithin (v x) (Icc 0 S) t = Real.exp (-v x t)*laplacian (h t) (fun y => v y t) x+
        (1-Real.exp (-v x t))*scalarCurvature (h t) x) :
    ∀ i z, z ∈ cylinder (F05D A i) a b →
      timeD (F05Q A i T) (pull A i u) z = Real.exp (-pull A i u z)*
        ((∑ j,∑ k,flatA (h z.2) A i z j k*spatialDD (pull A i u) z (realVec j) (realVec k))+
          ∑ j,flatB (h z.2) A i z j*spatialD (pull A i u) z (realVec j))+
        (1-Real.exp (-pull A i u z))*scalarCurvature (h z.2) (lift A i z.1) := by
  intro i z hz
  have hJets := F05_physical_slab_jets_congr hA hab ha hbT hbS u v hu hv hEq i z hz
  have hValue : pull A i u z = pull A i v z :=
    hEq (lift A i z.1) (F05D_lift_mem_closure hA hz.1) z.2 hz.2
  have hzV : z ∈ F05Q A i S := ⟨hz.1,ha.trans hz.2.1,hz.2.2.trans hbS⟩
  rw [hJets.2.2,hValue,hJets.1,hJets.2.1]
  exact F05_closed_nonlinear_chart_equation hA h v i (hv i) hVEq z hzV

theorem F05_encoded_nonlinear_equation {Q : Set (Point n)} {α : ℝ}
    (A : Mat n) (B : RIdx n → ℝ) (R : ℝ) (p F : Point n → ℝ)
    (hp : C2 Q p) (hF : C2 Q F) (v : F05JetComponent α Q) (z : Q)
    (hValue : v.1 z = F z.val) (hGrad : v.2.1 z = spatialD F z.val)
    (hHess : v.2.2.1.val.1 z = spatialDD F z.val)
    (hTime : v.2.2.2.val.1 z = timeD Q F z.val)
    (hEq : timeD Q (fun y => p y+F y) z.val = Real.exp (-(p z.val+F z.val))*
      ((∑ i,∑ j,A i j*spatialDD (fun y => p y+F y) z.val (realVec i) (realVec j))+
        ∑ i,B i*spatialD (fun y => p y+F y) z.val (realVec i))+
      (1-Real.exp (-(p z.val+F z.val)))*R) :
    timeD Q p z.val+v.2.2.2.val.1 z = Real.exp (-(p z.val+v.1 z))*
      ((∑ i,∑ j,A i j*(spatialDD p z.val+v.2.2.1.val.1 z) (realVec i) (realVec j))+
        ∑ i,B i*(spatialD p z.val+v.2.1 z) (realVec i))+
      (1-Real.exp (-(p z.val+v.1 z)))*R := by
  rw [hValue,hGrad,hHess,hTime]
  have hAdds := F05_native_add_jets hp hF z.property
  rw [hAdds.1,hAdds.2.1,hAdds.2.2] at hEq
  exact hEq

end Yau.Proofs.F05Aux

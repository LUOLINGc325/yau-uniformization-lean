import Yau.LeafProofs.L17BootstrapEvolutionJetsState
import Yau.LeafProofs.L17BackgroundLogDetJets
import Yau.LeafProofs.L17PotentialLeviMap

noncomputable section
open Set Metric Filter
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapEvolutionBindingAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapClosedSlabAux L17BootstrapEvolutionJetsAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

/-- Entrywise smoothness of the genuine Levi map, by its actual finite CLM evaluations. -/
theorem leviHessian_entry_contDiffOn {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {U : Set X} {H : X → D2 n} (hH : ContDiffOn ℝ ∞ H U) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun a => leviHessianCLM n (H a) i j) U := by
  have hEval (v w : ComplexVector n) : ContDiffOn ℝ ∞ (fun a => H a v w) U :=
    (hH.clm_apply (contDiffOn_const (c := v))).clm_apply (contDiffOn_const (c := w))
  have hRe : ContDiffOn ℝ ∞ (fun a => (1/4 : ℝ)*
      (H a (stdVec j) (stdVec i)+H a (Complex.I • stdVec j) (Complex.I • stdVec i))) U :=
    contDiffOn_const.mul ((hEval _ _).add (hEval _ _))
  have hIm : ContDiffOn ℝ ∞ (fun a => (1/4 : ℝ)*
      (H a (stdVec j) (Complex.I • stdVec i)-H a (Complex.I • stdVec j) (stdVec i))) U :=
    contDiffOn_const.mul ((hEval _ _).sub (hEval _ _))
  have hC := (Complex.ofRealCLM.contDiff.comp_contDiffOn hRe).add
    ((contDiffOn_const (c := Complex.I)).mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hIm))
  apply hC.congr
  intro a _ha
  apply Complex.ext <;> simp [leviHessianCLM_apply,leviFromHessian,Complex.mul_re,Complex.mul_im]

def evolutionJetMatrix (A : BoundedChartFamily g) (p : M.Carrier) (z0 : ComplexVector n)
    (s : State (ComplexVector n) 0) : Matrix (Fin n) (Fin n) ℂ :=
  pullbackMatrix g (A.chart p) (z0+s.1.1)+
    (s.1.2 : ℂ) • leviHessianCLM n (fderiv ℝ (fderiv ℝ (A.backgroundLogDet p)) (z0+s.1.1))+
    leviHessianCLM n (s.2 ⟨2,by decide⟩)

def evolutionJetBackgroundDet (A : BoundedChartFamily g) (p : M.Carrier) (z0 : ComplexVector n)
    (s : State (ComplexVector n) 0) : ℝ :=
  (pullbackMatrix g (A.chart p) (z0+s.1.1)).det.re

def evolutionJetDet (A : BoundedChartFamily g) (p : M.Carrier) (z0 : ComplexVector n)
    (s : State (ComplexVector n) 0) : ℝ := (evolutionJetMatrix A p z0 s).det.re

def evolutionSpatialDomain (A : BoundedChartFamily g) (z0 : ComplexVector n) :
    Set (State (ComplexVector n) 0) := {s | z0+s.1.1∈ball 0 A.radius}

/-- The domain is open in the full finite real jet space; it is not a PSD cone. -/
def evolutionPositiveJetDomain (A : BoundedChartFamily g) (p : M.Carrier) (z0 : ComplexVector n) :
    Set (State (ComplexVector n) 0) :=
  (evolutionSpatialDomain A z0 ∩ evolutionJetDet A p z0 ⁻¹' Ioi 0) ∩
    evolutionJetBackgroundDet A p z0 ⁻¹' Ioi 0

def evolutionJetLogDet (A : BoundedChartFamily g) (p : M.Carrier) (z0 : ComplexVector n)
    (s : State (ComplexVector n) 0) : ℝ :=
  Real.log (evolutionJetDet A p z0 s/evolutionJetBackgroundDet A p z0 s)

theorem evolutionSpatialDomain_isOpen (A : BoundedChartFamily g) (z0 : ComplexVector n) :
    IsOpen (evolutionSpatialDomain A z0) :=
  isOpen_ball.preimage (continuous_const.add continuous_fst.fst)

/-- Smoothness of matrix entries is used directly; no elementwise/Frobenius
norm or topology identification is assumed. -/
theorem evolutionJetMatrix_entry_smooth (A : BoundedChartFamily g) (p : M.Carrier)
    (z0 : ComplexVector n) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun s => evolutionJetMatrix A p z0 s i j) (evolutionSpatialDomain A z0) := by
  have hZ : ContDiff ℝ ∞ (fun s : State (ComplexVector n) 0 => z0+s.1.1) :=
    contDiff_const.add contDiff_fst.fst
  have hG := (A.coefficient_smooth p i j).comp hZ.contDiffOn (fun _ hs => hs)
  have hBg : ContDiffOn ℝ ∞
      (fun s : State (ComplexVector n) 0 => fderiv ℝ (fderiv ℝ (A.backgroundLogDet p)) (z0+s.1.1))
      (evolutionSpatialDomain A z0) :=
    (A.backgroundLogDet_hessian_smooth p).comp hZ.contDiffOn (fun _ hs => hs)
  have hQ : ContDiffOn ℝ ∞ (fun s : State (ComplexVector n) 0 => s.2 (⟨2,by decide⟩ : Fin 3))
      (evolutionSpatialDomain A z0) := by
    let L : State (ComplexVector n) 0 →L[ℝ] Jet (ComplexVector n) ℝ 2 :=
      (ContinuousLinearMap.proj (⟨2,by decide⟩ : Fin 3)).comp
        (ContinuousLinearMap.snd ℝ ((ComplexVector n) × ℝ) (JetPack (ComplexVector n) 2))
    exact L.contDiff.contDiffOn
  have hTime : ContDiffOn ℝ ∞ (fun s : State (ComplexVector n) 0 => (s.1.2 : ℂ))
      (evolutionSpatialDomain A z0) :=
    (Complex.ofRealCLM.contDiff.comp contDiff_fst.snd).contDiffOn
  have h := (hG.add (hTime.mul (leviHessian_entry_contDiffOn hBg i j))).add
    (leviHessian_entry_contDiffOn hQ i j)
  convert! h using 1 <;>
    simp only [evolutionJetMatrix,evolutionSpatialDomain,Function.comp_def,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]

theorem evolutionJetDet_smooth (A : BoundedChartFamily g) (p : M.Carrier) (z0 : ComplexVector n) :
    ContDiffOn ℝ ∞ (evolutionJetDet A p z0) (evolutionSpatialDomain A z0) :=
  Complex.reCLM.contDiff.comp_contDiffOn
    (SharedCalculus.contDiffOn_matrix_det (evolutionJetMatrix_entry_smooth A p z0))

theorem evolutionJetBackgroundDet_smooth (A : BoundedChartFamily g) (p : M.Carrier) (z0 : ComplexVector n) :
    ContDiffOn ℝ ∞ (evolutionJetBackgroundDet A p z0) (evolutionSpatialDomain A z0) := by
  have hZ : ContDiff ℝ ∞ (fun s : State (ComplexVector n) 0 => z0+s.1.1) :=
    contDiff_const.add contDiff_fst.fst
  exact Complex.reCLM.contDiff.comp_contDiffOn (SharedCalculus.contDiffOn_matrix_det
    (fun i j => (A.coefficient_smooth p i j).comp hZ.contDiffOn (fun _ hs => hs)))

theorem evolutionPositiveJetDomain_isOpen (A : BoundedChartFamily g) (p : M.Carrier)
    (z0 : ComplexVector n) : IsOpen (evolutionPositiveJetDomain A p z0) := by
  have hFirst : IsOpen (evolutionSpatialDomain A z0 ∩ evolutionJetDet A p z0 ⁻¹' Ioi 0) :=
    (evolutionJetDet_smooth A p z0).continuousOn.isOpen_inter_preimage
      (evolutionSpatialDomain_isOpen A z0) isOpen_Ioi
  exact ((evolutionJetBackgroundDet_smooth A p z0).continuousOn.mono inter_subset_left).isOpen_inter_preimage
    hFirst isOpen_Ioi

theorem evolutionJetLogDet_smooth (A : BoundedChartFamily g) (p : M.Carrier) (z0 : ComplexVector n) :
    ContDiffOn ℝ ∞ (evolutionJetLogDet A p z0) (evolutionPositiveJetDomain A p z0) := by
  have hA := (evolutionJetDet_smooth A p z0).mono
    (show evolutionPositiveJetDomain A p z0 ⊆ evolutionSpatialDomain A z0 from fun _ hs => hs.1.1)
  have hG := (evolutionJetBackgroundDet_smooth A p z0).mono
    (show evolutionPositiveJetDomain A p z0 ⊆ evolutionSpatialDomain A z0 from fun _ hs => hs.1.1)
  exact (hA.div hG (fun _ hs => hs.2.ne')).log (fun _ hs => (div_pos hs.1.2 hs.2).ne')

end Yau.LeafProofs.L17BootstrapEvolutionBindingAux

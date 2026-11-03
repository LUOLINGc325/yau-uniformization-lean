import Yau.Proofs.P06TimeIntegralPotentialPrimitive
import Yau.Proofs.P06Geometry

/-! The Levi operator commutes with the original time integral. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold
namespace Yau.NodeProofs.P06Aux.TimePotential
open Yau Yau.Blueprint Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Evaluation of a continuous multilinear map is a continuous linear map. -/
def jetEvalCLM (j : ℕ) (m : Fin j → E) : (E [×j]→L[ℝ] F) →L[ℝ] F where
  toFun A := A m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_eval_const m

variable {n : ℕ}
/-- The paper-convention Levi entry, as a fixed linear functional of the
actual second real derivative. -/
def leviJetCLM (a b : Fin n) :
    (ComplexVector n [×2]→L[ℝ] ℝ) →L[ℝ] ℂ :=
  (1 / 4 : ℂ) •
    ((Complex.ofRealCLM.comp (jetEvalCLM 2 ![stdVec b, stdVec a])) +
      (Complex.ofRealCLM.comp (jetEvalCLM 2 ![Complex.I • stdVec b, Complex.I • stdVec a])) +
      Complex.I • ((Complex.ofRealCLM.comp (jetEvalCLM 2 ![stdVec b, Complex.I • stdVec a])) -
        (Complex.ofRealCLM.comp (jetEvalCLM 2 ![Complex.I • stdVec b, stdVec a]))))

theorem leviC_eq_leviJetCLM {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (a b : Fin n) :
    leviC f z a b = leviJetCLM a b (iteratedFDeriv ℝ 2 f z) := by
  have hF : ContDiffAt ℝ 2 (fun y => (f y : ℂ)) z :=
    hf.continuousLinearMap_comp Complex.ofRealCLM
  have hdF := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [leviC, leviMatrix, L12Aux.wirt_wirtBar_eq_secondFDeriv hdF]
  simp only [L12Aux.secondFDeriv_ofReal hf]
  simp [leviJetCLM, jetEvalCLM, iteratedFDeriv_two_apply, smul_eq_mul]
  ring

variable {S : Set (ComplexVector n)} (hS : IsOpen S)
    {u : ℝ → ComplexVector n → ℝ} {f : ComplexVector n → ℝ}
    (hu : ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => u p.2 p.1) (S ×ˢ Ioi 0))
    (hf : ContDiffOn ℝ ∞ f S) (hinit : CompactJetInitial (S := S) u f)
include hS hu hf hinit

theorem leviC_intervalIntegrable {z : ComplexVector n} (hz : z ∈ S)
    {T : ℝ} (hT : 0 < T) (a b : Fin n) :
    IntervalIntegrable (fun s => leviC (u s) z a b) volume 0 T := by
  have hi := spatialJet_intervalIntegrable hS hu hf hinit 2 hz hT
  have hiL : IntervalIntegrable (fun s => leviJetCLM a b (iteratedFDeriv ℝ 2 (u s) z)) volume 0 T :=
    ⟨(leviJetCLM a b).integrable_comp hi.1, (leviJetCLM a b).integrable_comp hi.2⟩
  apply hiL.congr_uIoo
  intro s hs
  have harg : ContDiffAt ℝ ∞ (fun w : ComplexVector n => (w, s)) z :=
    contDiffAt_id.prodMk contDiffAt_const
  have hloc := (hu.contDiffAt ((hS.prod (isOpen_Ioi : IsOpen (Ioi (0 : ℝ)))).mem_nhds
    (show (z, s) ∈ S ×ˢ Ioi 0 from ⟨hz, (Set.uIoo_of_le hT.le ▸ hs).1⟩))).comp z harg
  exact (leviC_eq_leviJetCLM (by simpa only [Function.comp_def] using hloc.of_le (show (2 : ℕ∞ω) ≤ ∞ by simp)) a b).symm

theorem leviC_integral {z : ComplexVector n} (hz : z ∈ S)
    {T : ℝ} (hT : 0 < T) (a b : Fin n) :
    leviC (fun w => ∫ s in (0 : ℝ)..T, u s w) z a b =
      ∫ s in (0 : ℝ)..T, leviC (u s) z a b := by
  have hprimitive := (integral_contDiffOn hS hu hf hinit hT).contDiffAt (hS.mem_nhds hz)
  rw [leviC_eq_leviJetCLM (hprimitive.of_le (by simp)) a b,
    iteratedFDeriv_integral hS hu hf hinit 2 hz hT]
  rw [← (leviJetCLM a b).intervalIntegral_comp_comm
    (spatialJet_intervalIntegrable hS hu hf hinit 2 hz hT)]
  apply intervalIntegral.integral_congr_Ioo_of_le hT.le
  intro s hs
  have harg : ContDiffAt ℝ ∞ (fun w : ComplexVector n => (w, s)) z :=
    contDiffAt_id.prodMk contDiffAt_const
  have hloc := (hu.contDiffAt ((hS.prod (isOpen_Ioi : IsOpen (Ioi (0 : ℝ)))).mem_nhds
    (show (z, s) ∈ S ×ˢ Ioi 0 from ⟨hz, hs.1⟩))).comp z harg
  exact (leviC_eq_leviJetCLM (by simpa only [Function.comp_def] using hloc.of_le (show (2 : ℕ∞ω) ≤ ∞ by simp)) a b).symm

end Yau.NodeProofs.P06Aux.TimePotential

import Yau.Proofs.F01ANativeSpatialJetTower
import Yau.Proofs.F01ComplexLeviFrobenius
import Yau.Proofs.F01ScalarSymbolSmooth

/-! The genuine local potential log-determinant clock as a smooth scalar
function of the actual nested spatial state. The positive domain is open. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Frobenius

namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
open Yau.LeafProofs.L17BootstrapClosedSlabAux
open Yau.LeafProofs.L17BootstrapEvolutionJetsAux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def nativeFiniteClockMatrix (S : Point n → Matrix (Fin n) (Fin n) ℂ)
    (s : State (Space n) 0) : Matrix (Fin n) (Fin n) ℂ :=
  S s.1 + leviSecondMatrixCLM (s.2 ⟨2, by decide⟩)

def nativeFiniteClockScalar (S : Point n → Matrix (Fin n) (Fin n) ℂ)
    (b : Point n → ℝ) (s : State (Space n) 0) : ℝ :=
  Real.log (nativeFiniteClockMatrix S s).det.re + b s.1

def nativeFiniteClockDomain (S : Point n → Matrix (Fin n) (Fin n) ℂ)
    (Ω : Set (Point n)) : Set (State (Space n) 0) :=
  {s | s.1 ∈ Ω ∧ 0 < (nativeFiniteClockMatrix S s).det.re}

theorem nativeFiniteClockMatrix_contDiffOn
    (S : Point n → Matrix (Fin n) (Fin n) ℂ) {Ω : Set (Point n)}
    (hS : ContDiffOn ℝ ∞ S Ω) :
    ContDiffOn ℝ ∞ (nativeFiniteClockMatrix S) {s : State (Space n) 0 | s.1 ∈ Ω} := by
  let P : State (Space n) 0 →L[ℝ] (Space n →L[ℝ] Space n →L[ℝ] ℝ) :=
    (ContinuousLinearMap.proj (⟨2, by decide⟩ : Fin 3)).comp
      (ContinuousLinearMap.snd ℝ (Point n) (JetPack (Space n) 2))
  exact (hS.comp contDiffOn_fst (fun s hs => hs)).add
    ((leviSecondMatrixCLM (n := n)).contDiff.comp P.contDiff).contDiffOn

theorem nativeFiniteClockDet_contDiffOn
    (S : Point n → Matrix (Fin n) (Fin n) ℂ) {Ω : Set (Point n)}
    (hS : ContDiffOn ℝ ∞ S Ω) :
    ContDiffOn ℝ ∞ (fun s => (nativeFiniteClockMatrix S s).det.re)
      {s : State (Space n) 0 | s.1 ∈ Ω} :=
  Complex.reCLM.contDiff.comp_contDiffOn
    (frobenius_matrix_det_contDiff.comp_contDiffOn (nativeFiniteClockMatrix_contDiffOn S hS))

theorem nativeFiniteClockDomain_isOpen
    (S : Point n → Matrix (Fin n) (Fin n) ℂ) {Ω : Set (Point n)}
    (hΩ : IsOpen Ω) (hS : ContDiffOn ℝ ∞ S Ω) : IsOpen (nativeFiniteClockDomain S Ω) := by
  exact (nativeFiniteClockDet_contDiffOn S hS).continuousOn.isOpen_inter_preimage
    (hΩ.preimage continuous_fst) isOpen_Ioi

theorem nativeFiniteClockScalar_contDiffOn
    (S : Point n → Matrix (Fin n) (Fin n) ℂ) (b : Point n → ℝ) {Ω : Set (Point n)}
    (hS : ContDiffOn ℝ ∞ S Ω) (hb : ContDiffOn ℝ ∞ b Ω) :
    ContDiffOn ℝ ∞ (nativeFiniteClockScalar S b) (nativeFiniteClockDomain S Ω) := by
  have hDet := (nativeFiniteClockDet_contDiffOn S hS).mono
    (show nativeFiniteClockDomain S Ω ⊆ {s | s.1 ∈ Ω} from fun s hs => hs.1)
  exact (hDet.log (fun s hs => hs.2.ne')).add
    (hb.comp contDiffOn_fst (fun s hs => hs.1))

theorem nativeFiniteClockMatrix_actual
    (S : Point n → Matrix (Fin n) (Fin n) ℂ) (f : Point n → ℝ) (p : Point n)
    (hf : ContDiffAt ℝ 2 (fun z => f (z, p.2)) p.1) :
    nativeFiniteClockMatrix S (stateJ (nativeSpatialJet f) 0 p) =
      S p + leviC (fun z => f (z, p.2)) p.1 := by
  change S p + leviSecondMatrixCLM (nativeSpatialJet f 2 p) = _
  rw [nativeSpatialJet_two, leviSecondMatrixCLM_eq_native hf]

theorem nativeFiniteClockScalar_actual
    (S : Point n → Matrix (Fin n) (Fin n) ℂ) (b f : Point n → ℝ) (p : Point n)
    (hf : ContDiffAt ℝ 2 (fun z => f (z, p.2)) p.1) :
    nativeFiniteClockScalar S b (stateJ (nativeSpatialJet f) 0 p) =
      Real.log (S p + leviC (fun z => f (z, p.2)) p.1).det.re + b p := by
  rw [nativeFiniteClockScalar, nativeFiniteClockMatrix_actual S f p hf]
  rfl

end Yau.NodeProofs.F01Aux

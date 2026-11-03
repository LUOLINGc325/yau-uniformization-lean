import Yau.Proofs.F01LeviSpatialJetMap
import Yau.Proofs.F01FiniteTaylorComposition

/-! The finite matrix jet of background plus Levi potential is a
computed smooth function of the scalar jet two orders higher and
the original background jets. -/
noncomputable section
open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

def addSpatialJet {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ)
    (a b : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F := a + b

local instance matrixJetGroup (j : ℕ) : NormedAddCommGroup
    (ContinuousMultilinearMap ℝ (fun _ : Fin j => Space n) (Matrix (Fin n) (Fin n) ℂ)) :=
  ContinuousMultilinearMap.normedAddCommGroup'

local instance matrixJetSpace (j : ℕ) : NormedSpace ℝ
    (ContinuousMultilinearMap ℝ (fun _ : Fin j => Space n) (Matrix (Fin n) (Fin n) ℂ)) :=
  ContinuousMultilinearMap.normedSpace'

def potentialFiniteMatrixJet (k : ℕ) (S : Point n → Matrix (Fin n) (Fin n) ℂ)
    (p : Point n × FiniteTaylorJet (Space n) ℝ (k + 2)) :
    FiniteTaylorJet (Space n) (Matrix (Fin n) (Fin n) ℂ) k :=
  fun (j : Fin (k + 1)) =>
    addSpatialJet j.val (iteratedFDeriv ℝ j.val (fun z => S (z, p.1.2)) p.1.1)
      (leviSpatialJetCLM (n := n) j.val (p.2 ⟨j.val + 2, by omega⟩))

theorem potentialFiniteMatrixJet_native
    (k : ℕ) (S : Point n → Matrix (Fin n) (Fin n) ℂ) (q : Space n → ℝ)
    (p : Point n) {O : Set (Space n)} (hO : IsOpen O) (hp : p.1 ∈ O)
    (hS : ContDiffOn ℝ ∞ (fun z => S (z, p.2)) O) (hq : ContDiffOn ℝ ∞ q O) :
    potentialFiniteMatrixJet k S (p, fun j => iteratedFDeriv ℝ j.val q p.1) =
      (fun j : Fin (k + 1) => iteratedFDeriv ℝ j.val (fun z => S (z, p.2) + leviC q z) p.1) := by
  funext j
  change addSpatialJet j.val (iteratedFDeriv ℝ j.val (fun z => S (z, p.2)) p.1)
    (leviSpatialJetCLM (n := n) j.val (iteratedFDeriv ℝ (j.val + 2) q p.1)) = _
  rw [leviSpatialJetCLM_native hO hq j.val hp]
  exact (fun_iteratedFDeriv_add_apply
    ((hS.contDiffAt (hO.mem_nhds hp)).of_le (by simp))
    (((native_levi_frobenius_contDiffOn hO hq).contDiffAt (hO.mem_nhds hp)).of_le (by simp))).symm

theorem potentialFiniteMatrixJet_contDiffOn
    (k : ℕ) (S : Point n → Matrix (Fin n) (Fin n) ℂ) (W : Set (Point n))
    (hS : ∀ j : Fin (k + 1), ContDiffOn ℝ ∞
      (fun p : Point n => iteratedFDeriv ℝ j.val (fun z => S (z, p.2)) p.1) W) :
    ContDiffOn ℝ ∞ (potentialFiniteMatrixJet k S)
      {p : Point n × FiniteTaylorJet (Space n) ℝ (k + 2) | p.1 ∈ W} := by
  letI scalarJetGroups : (j : Fin (k + 2 + 1)) → NormedAddCommGroup
      (ContinuousMultilinearMap ℝ (fun _ : Fin j.val => Space n) ℝ) :=
    fun j => ContinuousMultilinearMap.normedAddCommGroup'
  letI scalarJetSpaces : (j : Fin (k + 2 + 1)) → NormedSpace ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin j.val => Space n) ℝ) :=
    fun j => ContinuousMultilinearMap.normedSpace'
  apply contDiffOn_pi.mpr
  intro j
  letI matrixJetGroup : NormedAddCommGroup
      (ContinuousMultilinearMap ℝ (fun _ : Fin j.val => Space n) (Matrix (Fin n) (Fin n) ℂ)) :=
    ContinuousMultilinearMap.normedAddCommGroup'
  letI matrixJetSpace : NormedSpace ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin j.val => Space n) (Matrix (Fin n) (Fin n) ℂ)) :=
    ContinuousMultilinearMap.normedSpace'
  have hFirst : ContDiffOn ℝ ∞
      (fun p : Point n × FiniteTaylorJet (Space n) ℝ (k + 2) =>
        iteratedFDeriv ℝ j.val (fun z => S (z, p.1.2)) p.1.1) {p | p.1 ∈ W} :=
    (hS j).comp contDiffOn_fst (fun p hp => hp)
  have hScalar : ContDiffOn ℝ ∞
      (fun p : Point n × FiniteTaylorJet (Space n) ℝ (k + 2) => p.2 ⟨j.val + 2, by omega⟩)
      {p | p.1 ∈ W} :=
    (contDiff_apply ℝ
      (fun i : Fin (k + 2 + 1) => ContinuousMultilinearMap ℝ (fun _ : Fin i.val => Space n) ℝ)
      ⟨j.val + 2, by omega⟩).comp_contDiffOn contDiffOn_snd
  have hSecond : ContDiffOn ℝ ∞
      (fun p : Point n × FiniteTaylorJet (Space n) ℝ (k + 2) =>
        leviSpatialJetCLM (n := n) j.val (p.2 ⟨j.val + 2, by omega⟩)) {p | p.1 ∈ W} :=
    (leviSpatialJetCLM (n := n) j.val).contDiff.comp_contDiffOn hScalar
  exact hFirst.add hSecond

end Yau.NodeProofs.F01Aux

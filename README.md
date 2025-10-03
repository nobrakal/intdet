## Overview
This project is the companion Rocq development of the paper
"All for One and One for All: Program Logics for Exploiting Internal Determinism in Parallel Programs".

## Setup & Build

See `INSTALL.md`.

## Architecture

Coq files are located in the `src/` directory.

* directory `lang` contains the syntax and semantics of the
  language we study.
* directory `musketeer` contains the Musketeer logic:
  + The Musketeer logic is defined as `triple` in `lockstep.v`.
  + Its adequacy theorem appears in `adequacy.v`
  + The ChainedLog logic is defined as `dwp` in `dwp.v`
  + Its adequacy theorem appears in `dwp_adequacy.v`
* directory `angelic` contains the angelic logic and its adequacy theorem.
* directory `types/affine` contains the MiniDet type system:
  + Syntactical rules are in `syntactical.v`
  + The soundness theorem is in `fundamental.v`.
* directory `types/lvar` contains a toy type system inspired by LVar.
* directory `utils` contains utility functions
* Code and examples are in `examples/`

## Links with the Paper

Coq files are located in the `src/` directory.

* Section 2.1:
  + the `dumas` example is covered in `examples/dumas.v`
  + code for the atomic counter is in `examples/counter.v`
* Figure 1:
  + specifications related to the counter are in `examples/counter.v`:
	- M-KSplit: `vcounter_split`
	- M-KRef: `triple_rref`
	- M-KAdd: `triple_ratomic_add`
	- M-KGet: `triple_rget`
  + Musketeer rules are in `musketeer/lockstep.v`:
    - M-Assert: `triple_assert`
	- M-Par: `triple_par`
* Figure 2:
  + specifications related to the counter are in `examples/counter.v`:
	- A-Ref: `run_rref`
    - A-Add: `run_ratomic_add`
	- A-Get: `run_rget`
  + Angelic rules are in `angelic/run.v`:
	- A-Assert: `run_assert`
	- A-ParSeqL: `run_par_seql`
	- A-ParSeqR: `run_par_seqr`
* Figure 3: syntactical definitions are in `lang/syntax.v`.
Projections are separated in two constructors. The active parallel tuple is called RunPar.
* Figure 4: the head reduction relation is in `lang/head_semantics.v`
* Figure 5: the main reduction relation is in `lang/semantics.v`
* Figure 6:
  + reducibility is defined in `lang/reducible.v`
  + NotStuck and Safe are defined in `musketeer/adequacy.v`
  + SISafety is defined in `musketeer/adequacy.v`. It differs from the paper:
  it has two parameters (two expressions), they will be instantiated
  by the same expression in the end. Moreover, it assumes that one
  expression is "closed", in the sense that it contains no locations
  initially (locations are runtime objects that should not appear in
  the program before execution).
* Theorem 4.1: stated in `musketeer/lockstep_adequacy.v`,
  lemma `triple_adequacy`
* Figure 7: Musketeer rules are in `musketeer/lockstep.v`
* Section 4.4:
  M-ElimExist is in `musketeer/lockstep.v`, lemma `triple_elim_exist`
* Theorem 5.1: stated in `musketeer/adequacy.v`, lemma `adequacy`.
Note that chained triples are implemented as "chained WPs",
where the left precondition should be specified with a magic wand, that is:
a chained triple `{ Pl } el { Ql | Pr } er { Qr }` is realized as `□ (Pl -∗ dwp ⊤ el Pr er Ql Qr)`
* Section 5.1:
  C-Chain in `musketeer/dwp.v`, lemma `dwpk_chain`
* Figure 8: Chained triples rules are in `musketeer/dwp.v`
* Figure 9: vProp is a standard Iris construct, see [https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/bi/monpred.v].
  In MonPred, the proposition is parameterized by a _monotonic_ property.
  In our case, the property is trivialized with the equality.
* Figure 10: in `musketeer/lockstep.v`, definition `triple`
* Figure 11: Angelic rules are in `angelic/run.v`
* Theorem 6.1: in `angelic/adequacy.v`, lemma `run_adequacy`
* Figure 12: syntax of MiniDet is in `types/affine/typing.v`
* Figure 13: syntactical rules are in `types/affine/syntactical.v`
* Figure 14:
  + shapes are in `types/affine/shape.v`
  + the logical relation is defined as `interp` in `types/affine/logrel.v`
* Lemma 7.1: in `types/affine/soundness.v`, lemma `soundness`
* Lemma 7.2: in `types/affine/soundness.v`, lemma `fundamental`
* Figure 15: in `examples/priority.v`
* Figure 16:
  + syntactical rules are in `types/affine/syntactical.v`
  + the update relation is `upd_typ` in `types/affine/typing.v`
* Figure 17:
  + triples for priority writes in `examples/priority.v`
  + logical relation in `types/affine/logrel.v`
  + the predicate ispw is called `is_priority_at_least`, the predicate ispr is `is_priority_is`
* Figure 18: in `examples/hashtbl.v`
* Figure 19: syntactical rules are in `types/affine/syntactical.v`.
  An IntSet is called a HashSet.
* Figure 20: compared to the paper, the Rocq development
supports hash sets with arbitrary element, but the user must provide
a total comparison function and a hash function. This implies additional
hypotheses that are trivially satisfied if the elements are integers and
the comparison function is `<`.
  + triples are in `examples/hashtbl.v`
  + logical relation in `types/affine/logrel.v`
* Figure 21:
  + parfor is defined in `examples/parfor.v`
  + dedup is defined in `examples/dedup.v`
* Section 7.4:
  + forspec is defined in `examples/parfor_seq.v`
  + angelic specification for dedup is in `examples/dedup_seq.v`

## Evaluation instructions

Users can check that all files compile and that no `Admitted` or `Axiom`
remains. It suffices to open the file `src/noaxioms.v` and play with it
interactively.
If the Coq command `Print Assumptions xxx` prints "Closed under the
global context", it indicates that `xxx` has no dependencies ([reference](https://coq.inria.fr/refman/proof-engine/vernacular-commands.html#coq:cmd.Print-Assumptions)).

Users can also open some selected `.v` files inside CoqIDE or Proof
General and evaluate the whole file to check that no errors occur and
to verify that the objects and statements mentioned in the claims are
what they are supposed to be.

## ProofGeneral

NB: There is a hack to work with ProofGeneral.
We have a dumb `src/_CoqProject` which makes visible the files
produced by dune.

See issue: https://github.com/ProofGeneral/PG/issues/477
